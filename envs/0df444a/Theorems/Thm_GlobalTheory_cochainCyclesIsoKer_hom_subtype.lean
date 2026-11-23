-- Prove2me | Theorems.Thm_GlobalTheory_cochainCyclesIsoKer_hom_subtype
-- name    : GlobalTheory.cochainCyclesIsoKer_hom_subtype
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:08.493841+00:00
-- url     : https://prove2.me/theorems/8a6c8162-6f18-407c-97b2-41c6d0f84ca9
-- title:
--   Global Theory: cochain Cycles Iso Ker hom subtype
-- statement:
--   The Global Theory construction uses the cochain Cycles Iso Ker hom subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L513-L518
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L513-L518

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]

theorem GlobalTheory.cochainCyclesIsoKer_hom_subtype (K : CochainComplex (ModuleCat.{v} R) ℕ) (p : ℕ)
    (f : K.X p →ₗ[R] K.X (p + 1)) (hf : K.d p (p + 1) = ModuleCat.ofHom f) :
    (cochainCyclesIsoKer K p f hf).hom ≫ ModuleCat.ofHom (LinearMap.ker f).subtype =
      K.iCycles p := by sorry
