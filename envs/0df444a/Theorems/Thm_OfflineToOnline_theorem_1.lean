-- Prove2me | Theorems.Thm_OfflineToOnline_theorem_1
-- name    : OfflineToOnline.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:07.211302+00:00
-- url     : https://prove2.me/theorems/30353273-30ad-41a9-8f49-bf6b68b5d28f
-- title:
--   Theorem 1 (corrected: $\log(d+1)$) — response-satisfiable iff $O(D(\boldsymbol p)\sqrt{\log d/T})$-approachable in $\ell_\infty$
-- statement:
--   Let $(\mathcal X,\mathcal Y,\boldsymbol p)$ be a Blackwell game with $\mathcal X,\mathcal Y$ compact and convex, $\mathcal X$ nonempty and $\boldsymbol p$ biaffine, and let $S\subseteq\mathbb R^d$ be closed, convex and nonempty. Let $D(\boldsymbol p)=\max_{x,y}\|\boldsymbol p(x,y)\|_\infty$.
--
--   1. **(if)** There is an absolute constant $c$ such that, whenever $S$ is response-satisfiable, for every horizon $T\ge1$ there is a measurable payoff-based player 1 strategy with actions in $\mathcal X$ that guarantees, against every sequence $y_1,\dots,y_T\in\mathcal Y$,
--
--   $$
--   d_\infty\Big(\frac1T\sum_{t=1}^T\boldsymbol p(x_t,y_t),\ S\Big)\ \le\ c\,D(\boldsymbol p)\sqrt{\frac{\log(d+1)}{T}} .
--   $$
--
--   2. **(only if)** If for every $\varepsilon>0$ some horizon $T\ge1$ and some player 1 strategy with actions in $\mathcal X$ guarantee $d_\infty\big(\frac1T\sum_t\boldsymbol p(x_t,y_t),S\big)\le\varepsilon$ against every sequence in $\mathcal Y$, then $S$ is response-satisfiable.
--
--   This is Blackwell's approachability theorem with the $\ell_\infty$ distance and a rate that depends on the dimension only through $\sqrt{\log d}$; applied to the orthant it provides the Blackwell algorithms of Theorem 2.
--
--   Differences from the source:
--   - correction: O(D(p) log(d)^{1/2} T^{−1/2}) → c · D(p) · √(log(d+1)/T); reason: at d = 1 the printed bound is 0 and false: X = Y = [0,1], p(x,y) = x − y, S = {0}, T = 1, player 2 forces distance ≥ 1/2; for d ≥ 2, log d ≤ log(d+1) ≤ 1.6 log d, so the O(·) is unchanged
--   - reading: O(·) → one constant c chosen before every parameter (m, k, d, X, Y, p, S, T); reason: the strongest reading of O(·)
--   - generalization: (if) S is approachable by some player 1 strategy → by a measurable, payoff-based strategy (it sees only its own actions and the realized payoffs); reason: a payoff-based strategy is a player 1 strategy (Remark 2, p.13); this is the form Algorithm 2 uses
--   - generalization: (only if) S is O(D(p) log(d)^{1/2} T^{−1/2})-approachable → for every ε > 0 some horizon T and some full-history strategy achieve distance ≤ ε; reason: a weaker hypothesis, implied by the printed one; p.24 notes the only if direction holds for any vanishing bound
--   - encoding: X, Y compact convex; S closed convex; d∞; player strategies → additionally X and S nonempty; Metric.infDist in Fin d → ℝ (sup norm); deterministic strategies against every sequence in Y, possibly depending on T; reason: Metric.infDist to ∅ is 0 and a game needs a player 1 action; against a deterministic strategy an adaptive player 2 is a sequence
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Theorem 1, p.12 (proof in Appendix B.2, pp.45–47)

import Mathlib
import Definitions.Def_OfflineToOnline_IsBiaffineOn
import Definitions.Def_OfflineToOnline_payoffDiam
import Definitions.Def_OfflineToOnline_IsResponseSatisfiable
import Definitions.Def_OfflineToOnline_payoffPlay
import Definitions.Def_OfflineToOnline_Approaches
import Definitions.Def_OfflineToOnline_fullHistoryPlay

namespace OfflineToOnline

/-- **Theorem 1** (corrected at `d = 1`: `log(d + 1)` for `log d`). A closed convex target set `S`
is `O(D(p) log(d)^{1/2} T^{−1/2})`-approachable in the Blackwell game `(X, Y, p)` if and only if
it is response-satisfiable, where `D(p)` is the ℓ∞ diameter of the payoffs and `d` the payoff
dimension. Stated as:

* (if) there is an absolute constant `c` such that for every game (`X`, `Y` compact convex, `X`
  nonempty, `p` biaffine), every closed convex nonempty response-satisfiable `S ⊆ ℝ^d` and every
  `T ≥ 1`, some measurable payoff-based strategy with actions in `X` keeps
  `d∞((1/T) ∑_t p(x_t, y_t), S) ≤ c · D(p) √(log(d + 1)/T)` against every sequence in `Y`;
* (only if) if for every `ε > 0` some horizon `T ≥ 1` and some full-history strategy with actions
  in `X` keep `d∞((1/T) ∑_t p(x_t, y_t), S) ≤ ε` against every sequence in `Y`, then `S` is
  response-satisfiable.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Theorem 1, p.12 (proof in Appendix B.2, pp.45–47).

Formalization Note: with `log d` the "if" part is false at `d = 1` (`X = Y = [0, 1]`,
`p(x, y) = x − y`, `S = {0}`, `T = 1`: the bound is `0`, but player 2 can force distance `≥ 1/2`);
for `d ≥ 2`, `log d ≤ log(d + 1) ≤ 1.6 log d`, so the O(·) is unchanged. The O(·) is one constant
`c` chosen before every parameter. `d∞` is `Metric.infDist` in `Fin d → ℝ`; `D(p)` is
`payoffDiam`. The "if" part produces a payoff-based, measurable strategy (it sees only its own
actions and the realized payoff vectors, Remark 2, p.13); the "only if" part assumes only an
`ε`-approach at some horizon by any full-history strategy (p.24: "the only if direction of this
theorem holds for any vanishing approachability bound"). Both are stronger than the printed
directions. -/
theorem theorem_1 :
    (∃ c : ℝ, ∀ {m k d : ℕ} (X : Set (Fin m → ℝ)) (Y : Set (Fin k → ℝ))
        (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ)) (S : Set (Fin d → ℝ)),
        IsCompact X → Convex ℝ X → X.Nonempty → IsCompact Y → Convex ℝ Y → IsBiaffineOn X Y p →
        IsClosed S → Convex ℝ S → S.Nonempty → IsResponseSatisfiable X Y p S →
        ∀ T : ℕ, 1 ≤ T → ∃ A : PayoffStrategy m d, (∀ t, Measurable (A t)) ∧
          Approaches p X Y S A T (c * payoffDiam p X Y * Real.sqrt (Real.log (d + 1) / T))) ∧
    (∀ {m k d : ℕ} (X : Set (Fin m → ℝ)) (Y : Set (Fin k → ℝ))
        (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ)) (S : Set (Fin d → ℝ)),
        IsCompact X → Convex ℝ X → X.Nonempty → IsCompact Y → Convex ℝ Y → IsBiaffineOn X Y p →
        IsClosed S → Convex ℝ S → S.Nonempty →
        (∀ ε : ℝ, 0 < ε → ∃ T : ℕ, 1 ≤ T ∧ ∃ B : FullHistoryStrategy m k,
          (∀ (t : ℕ) (h : Fin t → (Fin m → ℝ) × (Fin k → ℝ)), B t h ∈ X) ∧
          ∀ y : ℕ → Fin k → ℝ, (∀ t < T, y t ∈ Y) →
            Metric.infDist ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, p (fullHistoryPlay B y t) (y t)) S
              ≤ ε) →
        IsResponseSatisfiable X Y p S) := by sorry

end OfflineToOnline
