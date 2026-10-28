-- Prove2me | Theorems.Thm_OAI_Lech_PerfectDomainStages_stage_tensor_length_tendsto
-- name    : OAI.Lech.PerfectDomainStages.stage_tensor_length_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:41:07.018311+00:00
-- url     : https://prove2.me/theorems/22400e7b-9612-4496-b7ac-77405cf4bf37
-- title:
--   OAI.Lech.PerfectDomainStages.stage_tensor_length_tendsto: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.PerfectDomainStages`, with `open scoped TensorProduct ENNReal nonZeroDivisors Topology`, `open Filter`, `open Lech.RootTower`):
--
--   ```lean
--   theorem stage_tensor_length_tendsto
--       (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
--       (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
--         (IsLocalRing.ResidueField D)))
--       (M : ModuleCat.{u} D) (hM : IsFiniteLength D M) :
--       letI : ∀ n, Algebra D (stage (MvPowerSeries (Fin h) k) D p n) :=
--         fun n => (originalToStage (MvPowerSeries (Fin h) k) D p n).toAlgebra
--       Tendsto (fun n => normalizedLength (Fin h) k p
--         ((stage (MvPowerSeries (Fin h) k) D p n) ⊗[D] M)) atTop
--         (𝓝 (normalizedLength (Fin h) k p ((PerfectClosure D p) ⊗[D] M)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.PerfectDomainStages.domainAlgebra`, `OAI.Lech.RootTower.perfectAlgebra` and `OAI.Lech.RootTower.powerSeriesCharP` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.PerfectDomainStages.originalToStage` and `OAI.Lech.PerfectDomainStages.stage` (definitions bundle `OAIQ032L015` of this split); `OAI.Lech.RootTower.normalizedLength` (definitions bundle `OAIQ032L023` of this split).
--
--   **Used by.** The proof of `OAI.Lech.PerfectDomainStages.frobenius_module_length_tendsto` of this split imports it.
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

noncomputable section
open scoped TensorProduct ENNReal nonZeroDivisors Topology
open Filter
namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [CharP K p] [CharP L p]

include K L in

theorem stage_tensor_length_tendsto
    (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (M : ModuleCat.{u} D) (hM : IsFiniteLength D M) :
    letI : ∀ n, Algebra D (stage (MvPowerSeries (Fin h) k) D p n) :=
      fun n => (originalToStage (MvPowerSeries (Fin h) k) D p n).toAlgebra
    Tendsto (fun n => normalizedLength (Fin h) k p
      ((stage (MvPowerSeries (Fin h) k) D p n) ⊗[D] M)) atTop
      (𝓝 (normalizedLength (Fin h) k p ((PerfectClosure D p) ⊗[D] M))) := by
  sorry

end Lech.PerfectDomainStages

end

end OAI
end
