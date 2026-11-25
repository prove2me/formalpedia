-- Prove2me | Theorems.Thm_GlobalTheory_cechAbHMap_comp
-- name    : GlobalTheory.cechAbHMap_comp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:23.479748+00:00
-- url     : https://prove2.me/theorems/16b5907e-4ea9-5fe9-aa34-6584c2821ab0
-- title:
--   Global Theory: cech Ab HMap comp
-- statement:
--   The Global Theory construction uses the cech Ab HMap comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L525-L527
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L525-L527

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace Opposite
universe w v u
noncomputable section
open GlobalTheory
variable {T : Type w} [TopologicalSpace T] {ι : Type}
  (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) {Q Q' : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}}
  (V : Opens T) (U : ι → Opens T)
variable [LinearOrder ι]
variable {P}

theorem GlobalTheory.cechAbHMap_comp (φ : P ⟶ Q) (ψ : Q ⟶ Q') (n : ℕ) :
    cechAbHMap V U (φ ≫ ψ) n = cechAbHMap V U φ n ≫ cechAbHMap V U ψ n := by sorry
