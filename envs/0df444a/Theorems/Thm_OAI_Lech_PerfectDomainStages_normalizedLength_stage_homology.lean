-- Prove2me | Theorems.Thm_OAI_Lech_PerfectDomainStages_normalizedLength_stage_homology
-- name    : OAI.Lech.PerfectDomainStages.normalizedLength_stage_homology
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:37:22.181017+00:00
-- url     : https://prove2.me/theorems/b0d4d7d1-b29d-4c95-8f20-7b2c08bfd7ef
-- title:
--   OAI.Lech.PerfectDomainStages.normalizedLength_stage_homology: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.PerfectDomainStages`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex`, `open scoped TensorProduct ENNReal`, `open Lech.RootTower`):
--
--   ```lean
--   lemma normalizedLength_stage_homology
--       (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
--         (IsLocalRing.ResidueField D)))
--       (F : CochainComplex (ModuleCat.{u} D) ℤ) (hfin : ∀ j,Module.Finite D (F.X j))
--       (n : ℕ) (hi : Function.Injective (tensorMap (MvPowerSeries (Fin h) k) D p n)) (i : ℤ) :
--       normalizedLength (Fin h) k p ((stageComplex h k D p n F).homology i) =
--         ((p : ℝ≥0∞)^(n*h))⁻¹ *
--           (Module.length D ((Lech.frobeniusComplex D p n F).homology i)).toENNReal
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.PerfectDomainStages.domainAlgebra` and `OAI.Lech.RootTower.powerSeriesCharP` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.PerfectDomainStages.frobeniusComplexStagePowerSeriesIsDomain` and `OAI.Lech.RootTower.rootMap` (definitions bundle `OAIQ032L006` of this split); `OAI.Lech.PerfectDomainStages.stageComplex` and `OAI.Lech.PerfectDomainStages.tensorMap` (definitions bundle `OAIQ032L015` of this split); `OAI.Lech.RootTower.normalizedLength` (definitions bundle `OAIQ032L023` of this split); `OAI.Lech.frobeniusComplex` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proof of `OAI.Lech.PerfectDomainStages.frobenius_homology_conductor_bound` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L023

section

attribute [-instance] _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ENNReal

namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]

attribute [local instance] OAI.Lech.PerfectDomainStages.frobeniusComplexStagePowerSeriesIsDomain
lemma normalizedLength_stage_homology
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hfin : ∀ j,Module.Finite D (F.X j))
    (n : ℕ) (hi : Function.Injective (tensorMap (MvPowerSeries (Fin h) k) D p n)) (i : ℤ) :
    normalizedLength (Fin h) k p ((stageComplex h k D p n F).homology i) =
      ((p : ℝ≥0∞)^(n*h))⁻¹ *
        (Module.length D ((Lech.frobeniusComplex D p n F).homology i)).toENNReal := by
  sorry
end Lech.PerfectDomainStages

end

end OAI
end
