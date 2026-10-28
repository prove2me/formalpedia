-- Prove2me | Theorems.Thm_OAI_Lech_PerfectDomainStages_normalizedLength_actual_stage_quotient
-- name    : OAI.Lech.PerfectDomainStages.normalizedLength_actual_stage_quotient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:35:37.435995+00:00
-- url     : https://prove2.me/theorems/4562e0d3-bc74-4819-ba86-34ab5539acf1
-- title:
--   OAI.Lech.PerfectDomainStages.normalizedLength_actual_stage_quotient: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.PerfectDomainStages`, with `open MvPowerSeries`, `open scoped Classical`, `open scoped TensorProduct`, `open IsLocalRing`, `open MvPowerSeries IsLocalRing`, `open scoped ENNReal`, `open scoped ENNReal TensorProduct Classical DirectSum`, `open TensorProduct`, `open scoped TensorProduct nonZeroDivisors`, `open Lech.RootTower`, `open scoped ENNReal TensorProduct`):
--
--   ```lean
--   lemma normalizedLength_actual_stage_quotient
--       (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries σ k))
--         (IsLocalRing.ResidueField D))) (H : Ideal D) (n : ℕ)
--       (hi : Function.Injective (tensorMap (MvPowerSeries σ k) D p n)) :
--       normalizedLength σ k p ((stage (MvPowerSeries σ k) D p n) ⧸
--         H.map (originalToStage (MvPowerSeries σ k) D p n)) =
--       ((p : ℝ≥0∞) ^ (n * Fintype.card σ))⁻¹ *
--         (Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toENNReal
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.PerfectDomainStages.domainAlgebra` and `OAI.Lech.RootTower.powerSeriesCharP` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.PerfectDomainStages.tensorToStagePowerSeriesIsDomain` and `OAI.Lech.RootTower.rootMap` (definitions bundle `OAIQ032L006` of this split); `OAI.Lech.PerfectDomainStages.originalToStage`, `OAI.Lech.PerfectDomainStages.stage` and `OAI.Lech.PerfectDomainStages.tensorMap` (definitions bundle `OAIQ032L015` of this split); `OAI.Lech.RootTower.normalizedLength` (definitions bundle `OAIQ032L023` of this split).
--
--   **Used by.** The proof of `OAI.Lech.PerfectDomainStages.stage_tensor_length_tendsto` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L023

section

attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors

namespace Lech.PerfectDomainStages
open Lech.RootTower
open scoped ENNReal TensorProduct
variable (σ k D : Type*) [Fintype σ] [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [Algebra (MvPowerSeries σ k) D] [IsLocalHom (algebraMap (MvPowerSeries σ k) D)]
  [Module.Finite (MvPowerSeries σ k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]

attribute [local instance] OAI.Lech.PerfectDomainStages.tensorToStagePowerSeriesIsDomain
lemma normalizedLength_actual_stage_quotient
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries σ k))
      (IsLocalRing.ResidueField D))) (H : Ideal D) (n : ℕ)
    (hi : Function.Injective (tensorMap (MvPowerSeries σ k) D p n)) :
    normalizedLength σ k p ((stage (MvPowerSeries σ k) D p n) ⧸
      H.map (originalToStage (MvPowerSeries σ k) D p n)) =
    ((p : ℝ≥0∞) ^ (n * Fintype.card σ))⁻¹ *
      (Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toENNReal := by
  sorry

end Lech.PerfectDomainStages

end
end

end OAI
end
