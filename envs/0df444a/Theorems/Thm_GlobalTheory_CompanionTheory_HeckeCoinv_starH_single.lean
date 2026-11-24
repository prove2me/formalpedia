-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_starH_single
-- name    : GlobalTheory.CompanionTheory.HeckeCoinv.starH_single
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:47:06.695171+00:00
-- url     : https://prove2.me/theorems/d8fe6cdf-bbb2-4baf-8d40-2c051ad648e8
-- title:
--   Hecke Coinv: star H single
-- statement:
--   The Hecke Coinv construction uses the star H single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L210-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L210-L212

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
variable {G : Type} [Group G] {K : Subgroup G}

theorem GlobalTheory.CompanionTheory.HeckeCoinv.starH_single (hp : IsHeckePair K) (h : Hk K) (x : G ⧸ K) :
    (starH hp h).1 (Finsupp.single x 1) = rowF hp h x := by sorry
