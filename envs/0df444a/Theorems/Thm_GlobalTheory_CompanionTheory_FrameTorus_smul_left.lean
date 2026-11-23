-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_smul_left
-- name    : GlobalTheory.CompanionTheory.FrameTorus.smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:25.783234+00:00
-- url     : https://prove2.me/theorems/59310c80-cb0a-4eef-b479-da40cb84ead3
-- title:
--   Frame Torus: smul left
-- statement:
--   The Frame Torus construction uses the smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorusStatement.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorusStatement.lean#L50-L52

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

theorem GlobalTheory.CompanionTheory.FrameTorus.smul_left {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (a : L) (x y : V) :
    h (a • x) y = s a * h x y := by sorry
