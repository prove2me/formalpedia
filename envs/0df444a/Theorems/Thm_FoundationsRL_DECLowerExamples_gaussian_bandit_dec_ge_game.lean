-- Prove2me | Theorems.Thm_FoundationsRL_DECLowerExamples_gaussian_bandit_dec_ge_game
-- name    : FoundationsRL.DECLowerExamples.gaussian_bandit_dec_ge_game
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:22:09.062+00:00
-- url     : https://prove2.me/theorems/4324267f-3c2c-4fdc-891a-c9582ae455ff
-- title:
--   Example 6.4 (cont'd) — the Gaussian bandit's constrained DEC dominates a one-coordinate game
-- statement:
--   Let $\mathcal M=\mathcal M_{\mathrm{MAB\text{-}G}}$ be the Gaussian bandit class with $A$ actions, let $\widehat M(\pi)=\mathcal N(1/2,1)$ for every $\pi$, and let $\Delta\le 1/2$. Then for every $\varepsilon$,
--   $$
--   \mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M,\widehat M)\ \ge\ \inf_{p\in\Delta([A])}\ \max_i\Bigl\{(1-p(i))\Delta\ \Big|\ p(i)\frac{\Delta^2}{2}\le\varepsilon^2\Bigr\},
--   $$
--   where the constrained maximum is over the actions $i$ that satisfy the constraint, and is $0$ if there is none.
--
--   The bound comes from the sub-family $M_i(\pi)=\mathcal N(1/2+\Delta\,\mathbb I\{\pi=i\},1)$ of $\mathcal M$: under a decision distribution $p$, model $M_i$ has expected regret $(1-p(i))\Delta$ and expected squared Hellinger distance to $\widehat M$ at most $p(i)\Delta^2/2$. The inequality reduces the coefficient of the Gaussian bandit to a game on the masses $p(i)$, the first step toward $\mathrm{dec}^{\mathrm c}_\varepsilon\gtrsim\varepsilon\sqrt A$.
--
--   **Formalization Note** Actions are `Fin A` and $p(i)$ is the mass of $\{i\}$. Values are in $[0,\infty]$, so a negative $(1-p(i))\Delta$ counts as $0$. $\widehat M$ is the constant kernel.
--
--   Differences from the source:
--   - generalization: Δ such that the sub-family {M₁, …, M_A} lies in M, i.e. 1/2 + Δ ∈ [0, 1] → Δ ≤ 1/2; reason: for Δ < 0 the right-hand side is 0 (values in [0, ∞]) and the bound is trivial, so the statement specializes to the source's range
--   - encoding: max over i under the constraint → supremum over the feasible i, 0 when none; reason: the convention of footnote 15 (p. 104) for an empty constraint set
--   - encoding: real values → values in [0, ∞] (ENNReal.ofReal of (1 − p(i))Δ); reason: the coefficient is [0, ∞]-valued; for Δ ≥ 0 every term is the source's
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Example 6.4 (cont'd), p. 110, last display

import Mathlib
import Definitions.Def_FoundationsRL_DECLowerExamples_constrainedDECRef
import Definitions.Def_FoundationsRL_DECLowerExamples_gaussianBanditClass

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FoundationsRL.DECLowerExamples

/-- **Example 6.4 (cont'd), first part: the constrained DEC of the Gaussian bandit dominates a
one-coordinate game.** For `M = M_MAB-G` with `A` actions, `M̂(π) = N(1/2, 1)` and a parameter
`Δ ≤ 1/2` (so that the models `M_i` with `f^{M_i}(π) = 1/2 + Δ I{π = i}` lie in `M`),
`dec^c_ε(M, M̂) ≥ inf_{p∈Δ([A])} max_i { (1 − p(i))Δ | p(i)Δ²/2 ≤ ε² }`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Example 6.4 (cont'd), p. 110.

**Formalization Note.** Actions are `Fin A`; `p` ranges over probability measures on `Fin A` and
`p(i)` is `p {i}`. The constrained `max_i` is a supremum over the `i` that meet the constraint,
`0` when none does (the convention of footnote 15, p. 104); values are in `[0, ∞]`, so a negative
`(1 − p(i))Δ` counts as `0`. `M̂` is the constant kernel `π ↦ N(1/2, 1) ⊗ δ_∅`. -/
theorem gaussian_bandit_dec_ge_game (A : ℕ) (Δ : ℝ) (hΔ : Δ ≤ 1 / 2) (ε : ℝ) :
    (⨅ p : ProbabilityMeasure (Fin A), ⨆ (i : Fin A)
        (_ : (p {i} : ℝ) * (Δ ^ 2 / 2) ≤ ε ^ 2), ENNReal.ofReal ((1 - (p {i} : ℝ)) * Δ)) ≤
      constrainedDECRef ε (gaussianBanditClass A)
        (Kernel.const (Fin A) ((gaussianReal (1 / 2) 1).map (fun r => (r, ())))) := by sorry

end FoundationsRL.DECLowerExamples
