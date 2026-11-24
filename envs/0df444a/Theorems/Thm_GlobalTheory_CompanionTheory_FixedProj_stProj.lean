-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FixedProj_stProj
-- name    : GlobalTheory.CompanionTheory.FixedProj.stProj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:41:44.760826+00:00
-- url     : https://prove2.me/theorems/80babe5d-48c2-46bd-8b7e-0dbaabca058d
-- title:
--   Fixed Proj: st Proj
-- statement:
--   The Fixed Proj construction uses the st Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ProjectionStatement.lean#L10-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ProjectionStatement.lean#L10-L78

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ProjectionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FixedProj

theorem GlobalTheory.CompanionTheory.FixedProj.stProj : StProj := by sorry
