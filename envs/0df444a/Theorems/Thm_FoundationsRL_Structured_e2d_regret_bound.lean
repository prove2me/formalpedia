-- Prove2me | Theorems.Thm_FoundationsRL_Structured_e2d_regret_bound
-- name    : FoundationsRL.Structured.e2d_regret_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T20:19:36.410924+00:00
-- url     : https://prove2.me/theorems/5454e458-cc73-42f1-81ad-1dd6b9206454
-- title:
--   Proposition 13 — E2D regret bound (goal)
-- statement:
--   This theorem formalizes **Proposition 13** (Foster & Rakhlin, *Foundations of
--   Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 65,
--   attributed "Foster et al. [40]"), the capstone result of the chapter: the
--   **Estimation-to-Decisions (E2D)** algorithm's regret bound. Fix a finite decision space
--   $\Pi$, a function class $F$ containing the ground-truth reward function $f^\star$
--   (realizability, Assumption 5), and a maximizer selector `piStar` ($\pi_f$ an arg max of
--   $f$ on $\Pi$ for every $f \in F$). Suppose that at each round $t$ an online regression
--   oracle produces an estimate $\hat f_t \in \mathrm{co}(F)$, and E2D selects $p_t$ to (at
--   least) attain the value of the DEC game at $\hat f_t$ — i.e. $p_t$ certifies
--   $\mathrm{dec}_\gamma(F, \hat f_t)$ from above, as E2D's own minimizing choice does. If the
--   oracle's cumulative estimation error is bounded by $\mathrm{EstSq}$ (Definition 7), then
--   for every exploration parameter $\gamma > 0$, with probability at least $1-\delta$,
--
--   $$
--   \mathrm{Reg} \le \mathrm{dec}_\gamma(F) \cdot T + \gamma \cdot \mathrm{EstSq}(F, T, \delta).
--   $$
--
--   **Formalization Note** The book's own proof (pp. 65-66) bounds regret by an
--   *unconstrained* $\sup_{\hat f : \Pi \to \mathbb{R}} \mathrm{dec}_\gamma(F, \hat f) \cdot T +
--   \gamma \cdot \mathrm{EstSq}$, and only equates this with the official
--   $\mathrm{dec}_\gamma(F) \cdot T$ (Eq. (4.16), a sup over $\mathrm{co}(F)$) via Proposition
--   24 — a fact stated on p. 80, outside this chunk's page range, whose own proof is deferred
--   to Exercise 10 and not otherwise given in the chapter. Rather than invoke that
--   unproven-in-range reduction, this formalization adds the explicit hypothesis
--   `hfhat : ∀ t, fhat t ∈ convexHull ℝ F`, matching how the book itself describes E2D's
--   oracle output ("online estimation algorithms such as exponential weights will produce
--   improper predictions with $\hat f \in \mathrm{co}(F)$", p. 65) — so the conclusion's
--   $\mathrm{dec}_\gamma(F)$ (already a sup over $\mathrm{co}(F)$ by definition) directly
--   dominates each round's $\mathrm{dec}_\gamma(F, \hat f_t)$ without appeal to Proposition
--   24. The probability-$1-\delta$ qualifier is captured, as elsewhere in this series, via the
--   explicit `OracleGuarantee` hypothesis on the realized run.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 65, Proposition 13

import Mathlib
import Definitions.Def_FoundationsRL_Structured_DEC
import Definitions.Def_FoundationsRL_Structured_OracleGuarantee
import Definitions.Def_FoundationsRL_Structured_regret

namespace FoundationsRL.Structured

/-- Proposition 13 (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
Decision Making*, arXiv:2312.16730v1, p. 65, attributed "Foster et al. [40]"): the
Estimation-to-Decisions (E2D) algorithm's regret bound. Given a finite decision space `Π`, a
function class `F` containing the ground-truth reward function `fstar` (Assumption 5), and a
maximizer selector `piStar` (`piStar f` is `π_f`, an arg max of `f` on `Π`, for every `f ∈ F`),
suppose at each round `t` the online regression oracle produces `fhat t` and E2D selects `p t`
to (at least) attain the value of the min-max game defining `decγ(F, f̂_t)` — i.e. `p t`
certifies `decγ(F, f̂_t)` from above, as the E2D algorithm's minimizing choice does. If the
oracle's cumulative estimation error is bounded by `EstSq` (`OracleGuarantee`), then the regret
of the realized run is at most `decγ(F) · T + γ · EstSq(F, T, δ)` (Eq. (4.17)).

The book's own proof (p. 65-66) bounds regret by `sup_{f̂ : Π → ℝ} decγ(F, f̂) · T + γ ·
EstSq`, an unconstrained sup, and only equates this with `decγ(F) · T` (`decγ(F)` officially
`sup_{f̂∈co(F)} decγ(F,f̂)` by Eq. (4.16)) via Proposition 24 — a fact stated on p. 80, outside
this chunk's page range, whose own proof is left to Exercise 10 and is not otherwise given in
the chapter. Rather than invoke that unproven-in-range reduction, this formalization adds the
hypothesis that each round's oracle estimate `f̂_t` already lies in `co(F)`, matching how the
book itself describes E2D's oracle ("online estimation algorithms such as exponential weights
will produce improper predictions with f̂ ∈ co(F)", p. 65) — so the conclusion's `decγ(F)` (Eq.
4.16, over `co(F)`) directly dominates each round's `decγ(F, f̂_t)` without appeal to Prop. 24. -/
theorem e2d_regret_bound {S : Type*} [Fintype S] (F : Set (S → ℝ))
    (piStar : (S → ℝ) → S) (hpiStar : ∀ f ∈ F, ∀ π, f π ≤ f (piStar f))
    (fstar : S → ℝ) (hfstar : fstar ∈ F)
    (T : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (fhat : Fin T → S → ℝ) (hfhat : ∀ t, fhat t ∈ convexHull ℝ F)
    (p : Fin T → S → ℝ)
    (hp_nonneg : ∀ t π, 0 ≤ p t π) (hp_sum : ∀ t, ∑ π, p t π = 1)
    (hp_min : ∀ t, ∀ f ∈ F,
      ∑ π, p t π * (f (piStar f) - f π - γ * (f π - fhat t π) ^ 2) ≤ decGf F piStar γ (fhat t))
    (EstSq : ℝ) (hOracle : OracleGuarantee T fhat fstar p EstSq) :
    regret fstar (piStar fstar) T p ≤ dec F piStar γ * T + γ * EstSq := by sorry

end FoundationsRL.Structured
