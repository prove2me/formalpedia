-- Prove2me | Theorems.Thm_GlobalTheory_cechAbHMap_add
-- name    : GlobalTheory.cechAbHMap_add
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:30.409449+00:00
-- url     : https://prove2.me/theorems/5c966836-ee62-4df1-961e-48c5f26d466f
-- title:
--   Global Theory: cech Ab HMap add
-- statement:
--   The Global Theory construction uses the cech Ab HMap add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L531-L533
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L531-L533

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

theorem GlobalTheory.cechAbHMap_add (φ ψ : P ⟶ Q) (n : ℕ) :
    cechAbHMap V U (φ + ψ) n = cechAbHMap V U φ n + cechAbHMap V U ψ n := by sorry
