-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_isIso_inv
-- name    : GlobalTheory.CompanionTheory.FlDecomp.isIso_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:11.083492+00:00
-- url     : https://prove2.me/theorems/159214f3-7119-48d1-9512-66dd93bb7c89
-- title:
--   Fl Decomp: is Iso inv
-- statement:
--   The Fl Decomp construction uses the is Iso inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L18-L24

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

theorem GlobalTheory.CompanionTheory.FlDecomp.isIso_inv {h : V → V → L} {a : V ≃ₗ[L] V} (ha : IsIso h a) : IsIso h a⁻¹ := by sorry
