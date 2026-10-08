-- Prove2me | Theorems.Thm_MitigateSupplyRisk_DualSourcing_theorem_1
-- name    : MitigateSupplyRisk.DualSourcing.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:55.638603+00:00
-- url     : https://prove2.me/theorems/5c5d7312-4a30-4192-8695-cb97c19c5fd6
-- title:
--   Theorem 1, p. 494 — an optimal q* with q_i* = 0, q_i* = K_i, or ∇_{q_i}Π₂(q*; a) = 0
-- statement:
--   Consider the two-supplier random-capacity newsvendor with expected profit $\Pi_2(q; a)$ (Eq. (3)), and suppose that demand $X \ge 0$ has a density and finite mean.
--
--   Then there is an optimal procurement vector $q^* = (q_1^*, q_2^*)$, that is, $q^* \ge 0$ with $\Pi_2(q; a) \le \Pi_2(q^*; a)$ for every $q \ge 0$, such that for each supplier $i = 1, 2$
--   $$q_i^* = 0, \qquad q_i^* = K_i, \qquad \text{or} \qquad \nabla_{q_i} \Pi_2(q^*; a) = 0.$$
--
--   The theorem has two parts: a maximizer exists, although the feasible set $q \ge 0$ is unbounded, and each of its coordinates is at a boundary ($0$ or the design capacity) or at a stationary point of the profit in that coordinate. It is the starting point for the first-order condition (6).
--
--   **Formalization Note.** The printed statement reads "$q_i^* = K$"; there is no un-indexed $K$ in the paper, and it means the design capacity $K_i$. The partial derivative is the derivative at $q_i^*$ of $t \mapsto \Pi_2(q^*$ with $q_i^*$ replaced by $t; a)$, and the third alternative asserts that this derivative exists and equals $0$. The density of demand is the paper's standing assumption of §3.1, expressed as absolute continuity of the demand law with respect to Lebesgue measure.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 494 (PDF p. 6), Theorem 1

import Mathlib
import Definitions.Def_MitigateSupplyRisk_DualSourcing_Model

open MeasureTheory ProbabilityTheory

namespace MitigateSupplyRisk.DualSourcing

/-- Theorem 1 (Wang, Gilland, Tomlin 2010, p. 494): when demand has a density, there is an optimal
procurement vector `q*` (a maximizer of `Π₂(·; a)` over `q ≥ 0`) such that for each supplier
`i`, either `q*_i = 0`, or `q*_i = K_i`, or the partial derivative of `Π₂(·; a)` in `q_i`
exists at `q*` and equals `0`. -/
theorem theorem_1 (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμint : Integrable id μ) (hμac : μ ≪ volume)
    (a : Fin 2 → ℝ) :
    ∃ q, M.IsOptimal μ a q ∧
      ∀ i : Fin 2, q i = 0 ∨ q i = M.K i ∨
        HasDerivAt (fun t => M.Pi2 μ (Function.update q i t) a) 0 (q i) := by sorry

end MitigateSupplyRisk.DualSourcing
