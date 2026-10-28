-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_regular_node_pointwise_sat
-- name    : OAI.DilutedSpinGlass.UniversalDictionary.regular_node_pointwise_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:20:53.506574+00:00
-- url     : https://prove2.me/theorems/f750576d-5258-4e43-8c7f-eb6d201a2014
-- title:
--   OAI.DilutedSpinGlass.UniversalDictionary.regular_node_pointwise_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.UniversalDictionary.regular_node_pointwise` of [lean/OAI/Probability/DilutedSpin/RegularNodeProducer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/RegularNodeProducer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.UniversalDictionary`, with `open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir`, `open ReducedTopology`, `open scoped NNReal BigOperators`):
--
--   ```lean
--   theorem regular_node_pointwise_sat (M : Model p) (θB hB : ℝ) (L : ℕ)
--       (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
--       {η : ℝ} (hη : 0<η) (hlarge : 1<η*(L+1:ℕ))
--       (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1))
--       (hQ : regularShapeDomain (.node k hk C) (L+1) η Q) :
--       ∃ (S T : PrescribedTree (L+1)) (a : S.Leaf)
--         (q : Option (Fin (2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+1)) → T.Leaf)
--         (J : ℝ), ∀ (N : ℕ) (u : Spec L × ℕ → ℝ),
--       η*physicalScheduledEnergy M θB hB N L u (.node k hk C) Q ≤
--         4*((L+1:ℕ):ℝ)⁻¹ +
--         2*(|physicalTreeMatrixCovariance (gridExponents L) S a M θB hB N u T q|/|J|) +
--         4*nodeChargeConstant k hk C η*Real.sqrt (physicalChildMass M θB hB N L u k hk C true Q) +
--         2*nodeChargeConstant k hk C η*physicalNodeShift M θB hB N L u k hk C Q +
--         (4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ))*
--           Real.sqrt (physicalChildMass M θB hB N L u k hk C false Q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.Model` (the published bundle `Def_DilutedSpin`); `OAI.DilutedSpinGlass.PrescribedTree`, `OAI.DilutedSpinGlass.ReducedTopology`, `OAI.DilutedSpinGlass.PrescribedTree.Leaf`, `OAI.DilutedSpinGlass.ReducedTopology.Leaf`, `OAI.DilutedSpinGlass.ReducedTopology.Vertex`, `OAI.DilutedSpinGlass.ReducedTopology.leafFintype`, `OAI.DilutedSpinGlass.ReducedTopology.nodeChargeConstant`, `OAI.DilutedSpinGlass.ReducedTopology.nodeHistoryBudget`, `OAI.DilutedSpinGlass.ReducedTopology.regularShapeDomain`, `OAI.DilutedSpinGlass.UniversalDictionary.Spec`, `OAI.DilutedSpinGlass.UniversalDictionary.gridExponents`, `OAI.DilutedSpinGlass.UniversalDictionary.physicalChildMass`, `OAI.DilutedSpinGlass.UniversalDictionary.physicalNodeShift`, `OAI.DilutedSpinGlass.UniversalDictionary.physicalScheduledEnergy` and `OAI.DilutedSpinGlass.UniversalDictionary.physicalTreeMatrixCovariance` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/RegularNodeProducer.lean (declaration OAI.DilutedSpinGlass.UniversalDictionary.regular_node_pointwise)

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000

section

attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
variable {p : ℕ}
attribute [local irreducible] projectionShiftError matrixProjectionError oldProjectionError
    matrixObservableHistory KernelTower.halfTripleDifferenceAt splitProjector

theorem regular_node_pointwise_sat (M : Model p) (θB hB : ℝ) (L : ℕ)
    (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    {η : ℝ} (hη : 0<η) (hlarge : 1<η*(L+1:ℕ))
    (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1))
    (hQ : regularShapeDomain (.node k hk C) (L+1) η Q) :
    ∃ (S T : PrescribedTree (L+1)) (a : S.Leaf)
      (q : Option (Fin (2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+1)) → T.Leaf)
      (J : ℝ), ∀ (N : ℕ) (u : Spec L × ℕ → ℝ),
    η*physicalScheduledEnergy M θB hB N L u (.node k hk C) Q ≤
      4*((L+1:ℕ):ℝ)⁻¹ +
      2*(|physicalTreeMatrixCovariance (gridExponents L) S a M θB hB N u T q|/|J|) +
      4*nodeChargeConstant k hk C η*Real.sqrt (physicalChildMass M θB hB N L u k hk C true Q) +
      2*nodeChargeConstant k hk C η*physicalNodeShift M θB hB N L u k hk C Q +
      (4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ))*
        Real.sqrt (physicalChildMass M θB hB N L u k hk C false Q) := by
  sorry

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end
