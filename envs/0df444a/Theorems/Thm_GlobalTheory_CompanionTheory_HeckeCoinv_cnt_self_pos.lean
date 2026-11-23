-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_cnt_self_pos
-- name    : GlobalTheory.CompanionTheory.HeckeCoinv.cnt_self_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:49.116227+00:00
-- url     : https://prove2.me/theorems/8b43ce2b-3f38-472b-b150-83bb1312bff7
-- title:
--   Hecke Coinv: cnt self pos
-- statement:
--   The Hecke Coinv construction uses the cnt self pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L38-L41

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
open scoped InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeCoinv
variable (Γ : Type) {X : Type} [Group Γ] [MulAction Γ X]
variable {Γ}

theorem GlobalTheory.CompanionTheory.HeckeCoinv.cnt_self_pos [∀ x : X, Finite (MulAction.stabilizer Γ x)] (x : X) : 0 < cnt Γ x x := by sorry
