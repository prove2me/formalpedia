-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_add_left
-- name    : GlobalTheory.CompanionTheory.FrameTorus.add_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:41:13.641729+00:00
-- url     : https://prove2.me/theorems/4771cdbf-ff25-4afd-b3f8-df51a7b19698
-- title:
--   Frame Torus: add left
-- statement:
--   The Frame Torus construction uses the add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorusStatement.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorusStatement.lean#L46-L48

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrameTorus
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

theorem GlobalTheory.CompanionTheory.FrameTorus.add_left {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (x x' y : V) :
    h (x + x') y = h x y + h x' y := by sorry
