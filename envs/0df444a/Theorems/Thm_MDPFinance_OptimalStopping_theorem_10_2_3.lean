-- Prove2me | Theorems.Thm_MDPFinance_OptimalStopping_theorem_10_2_3
-- name    : MDPFinance.OptimalStopping.theorem_10_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:44:53.73002+00:00
-- url     : https://prove2.me/theorems/19168695-629f-4a14-b1f4-c1a0081f2dab
-- title:
--   Theorem 10.2.3 — existence of an optimal stopping region via the limit of the d_n
-- statement:
--   **Theorem 10.2.3** (p. 313). Suppose a stopping problem with unbounded horizon is given.
--   Then it holds:
--
--   a) The limit $d := \lim_{n\to\infty} d_n$ exists. Define $S^* := \{x \in E \mid d(x) \ge 0\}$; then
--      $S^* = \bigcap_n S_n^* = \{x \in E \mid J(x) = g(x)\}$ and $f^* := \mathbf 1_{S^*}$ is a
--      maximizer of $J$.
--   b) If $G_{f^*} \ge \mathcal{T}G_{f^*}$ and $\mathbb{P}_x(\tau_{f^*} < \infty) = 1$ for all
--      $x \in E$, then $\tau^* := \inf\{n \in \mathbb{N}_0 \mid X_n \in S^*\}$ is an optimal stopping
--      time and $G_{f^*}(x) = \mathbb{E}_x[R_{\tau^*}] = V_\infty^*(x)$, $x \in E$.
--
--   The route to an optimal *rule* that Theorem 10.2.2 does not give: 10.2.2 characterizes the value,
--   10.2.3 produces the stopping region. The limit exists because the $d_n$ are monotone, which is
--   Theorem 10.1.5 b) in another guise.
--
--   **b) is conditional on two hypotheses and both are the book's.** $G_{f^*} \ge \mathcal{T}G_{f^*}$
--   says the rule's own value is $c$-superharmonic; $\mathbb{P}_x(\tau_{f^*} < \infty) = 1$ says the
--   rule actually stops. Drop either and the conclusion fails: a rule whose entry time is infinite with
--   positive probability collects the $\tau = \infty$ reward, which the book leaves undefined.
--
--   The triple equality $G_{f^*} = \mathbb{E}_x[R_{\tau^*}] = V_\infty^*$ is what "optimal" means here,
--   so it is stated as attainment — the expected reward *is* the least upper bound — not as an
--   inequality, which every stopping time satisfies by definition of the supremum.
--
--   **Moderation note.** As for Theorem 10.2.2 (`J` now the model's limit); b)'s conclusion uses the book's optimality notion (`IsOptimal`: stopping time, a.s. finite, attains `V_∞^*`) together with `G_{f^*} = 𝔼_x[R_{τ^*}]`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 313 (PDF 320), Theorem 10.2.3

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory Filter Topology

namespace MDPFinance.OptimalStopping

/-- **Theorem 10.2.3** (p. 313), under (B). a) `d := lim_n d_n` exists; with `S^* := {d ≥ 0}`,
`S^* = ∩_n S_n^* = {J = g}` and `f^* := 1_{S^*}` is a maximizer of `J`. b) If `G_{f^*} ≥ T G_{f^*}`
and `ℙ_x(τ_{f^*} < ∞) = 1` for all `x`, then `τ^* := inf{n | X_n ∈ S^*}` is an optimal stopping
time and `G_{f^*}(x) = 𝔼_x[R_{τ^*}] = V_∞^*(x)`. -/
theorem theorem_10_2_3 {E : Type*} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr) :
    (∃ d : E → EReal,
      (∀ x : E, Tendsto (fun n => P.d n x) atTop (𝓝 (d x))) ∧
      ({x : E | 0 ≤ d x} = ⋂ n : ℕ, P.stopSet n) ∧
      ({x : E | 0 ≤ d x} = {x : E | P.Jlim x = (P.g x : EReal)}) ∧
      P.IsMaximizer {x : E | 0 ≤ d x} P.Jlim) ∧
    ((∀ x : E, P.T (P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)}) x ≤
        P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)} x) →
      (∀ x : E, Pr x {w | P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)} w = ⊤} = 0) →
      P.IsOptimal Pr (P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)}) ∧
        ∀ x : E, P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)} x =
          P.EReward Pr (P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)}) x) := by sorry

end MDPFinance.OptimalStopping
