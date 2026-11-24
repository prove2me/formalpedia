-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_isIso_mul
-- name    : GlobalTheory.CompanionTheory.FlDecomp.isIso_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:41:27.70796+00:00
-- url     : https://prove2.me/theorems/251966b9-d3cb-4879-bc51-2e9e2699e95d
-- title:
--   Fl Decomp: is Iso mul
-- statement:
--   The Fl Decomp construction uses the is Iso mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L15-L16

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlDecomp
open CompanionTheory.Rg.FlB
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

theorem GlobalTheory.CompanionTheory.FlDecomp.isIso_mul {h : V → V → L} {a b : V ≃ₗ[L] V} (ha : IsIso h a) (hb : IsIso h b) : IsIso h (a * b) := by sorry
