-- Prove2me | Theorems.Thm_MDPFinance_OptimalStopping_corollary_10_2_6
-- name    : MDPFinance.OptimalStopping.corollary_10_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:45:03.8579+00:00
-- url     : https://prove2.me/theorems/def631ad-6910-4b1c-b988-8312b0bd5ce0
-- title:
--   Corollary 10.2.6 — three sufficient conditions for optimality of τ_{f*}
-- statement:
--   **Corollary 10.2.6** (p. 315). Suppose a stopping problem with unbounded horizon is given
--   and $f^*$ is a maximizer of $J$. Then it holds:
--
--   a) If the corresponding Markov Decision Problem has a bounding function $b$ with
--      $\beta\alpha_b < 1$, then $G_{f^*} = J$. Moreover, if
--      $\mathbb{P}_x(\tau_{f^*} < \infty) = 1$ for all $x \in E$ then $\tau_{f^*}$ is an optimal
--      stopping time.
--   b) If $\sup_{x \in E} c(x) < 0$, $\beta = 1$ and $G_{f^*} = J$, then
--      $\mathbb{P}_x(\tau_{f^*} < \infty) = 1$ for all $x \in E$ and $\tau_{f^*}$ is an optimal
--      stopping time.
--   c) If $J - g$ is bounded from above and $\mathbb{P}_x(\tau_{f^*} < \infty) = 1$ for all $x \in E$,
--      then $\tau_{f^*}$ is an optimal stopping time and $G_{f^*} = J$.
--
--   Theorem 10.2.3 b) needs two things — that the rule's value is $c$-superharmonic and that the rule
--   stops almost surely — and neither is free. This corollary is the practical entry point: three
--   separately checkable conditions, each of which delivers one or both.
--
--   The three are genuinely different and none subsumes another. a) is a contraction argument
--   ($\beta\alpha_b < 1$); b) buys almost sure finiteness from a strictly negative running reward, so
--   waiting forever costs infinitely much, and it is the *undiscounted* case $\beta = 1$ where a) is
--   unavailable; c) assumes finiteness instead and buys $G_{f^*} = J$ from a one-sided bound on
--   $J - g$.
--
--   Note the direction of each implication. In a) and c) almost sure finiteness is a **hypothesis**; in
--   b) it is a **conclusion**. Stating b)'s finiteness as a hypothesis would lose the sharpest part of
--   the corollary.
--
--   **Moderation note.** The bounding function is Chapter 7's (`b ≥ 0`, constant `c_r`, Lebesgue drift bound); `J − g` bounded above is stated in `[-∞,∞]`; optimality via `IsOptimal`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 315 (PDF 322), Corollary 10.2.6

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory Filter Topology

namespace MDPFinance.OptimalStopping

/-- **Corollary 10.2.6** (p. 314), under (B), for a maximizer `f^* = 1_S` of `J`. a) If the
Markov Decision Model has a bounding function `b` with `βα_b < 1`, then `G_{f^*} = J`; if moreover
`ℙ_x(τ_{f^*} < ∞) = 1` for all `x`, `τ_{f^*}` is optimal. b) If `sup c < 0`, `β = 1` and
`G_{f^*} = J`, then `ℙ_x(τ_{f^*} < ∞) = 1` for all `x` and `τ_{f^*}` is optimal. c) If `J − g` is
bounded above and `ℙ_x(τ_{f^*} < ∞) = 1` for all `x`, then `τ_{f^*}` is optimal and
`G_{f^*} = J`. -/
theorem corollary_10_2_6 {E : Type*} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr)
    (S : Set E) (hS : P.IsMaximizer S P.Jlim) :
    (∀ B : P.BoundingFunction, P.beta * B.alpha < 1 →
      (∀ x : E, P.Gf Pr S x = P.Jlim x) ∧
      ((∀ x : E, Pr x {w | P.ruleTime S w = ⊤} = 0) → P.IsOptimal Pr (P.ruleTime S))) ∧
    ((∃ s : ℝ, s < 0 ∧ ∀ x : E, P.c x ≤ s) → P.beta = 1 → (∀ x : E, P.Gf Pr S x = P.Jlim x) →
      (∀ x : E, Pr x {w | P.ruleTime S w = ⊤} = 0) ∧ P.IsOptimal Pr (P.ruleTime S)) ∧
    ((∃ C : ℝ, ∀ x : E, P.Jlim x ≤ (P.g x : EReal) + (C : EReal)) →
      (∀ x : E, Pr x {w | P.ruleTime S w = ⊤} = 0) →
      P.IsOptimal Pr (P.ruleTime S) ∧ ∀ x : E, P.Gf Pr S x = P.Jlim x) := by sorry

end MDPFinance.OptimalStopping
