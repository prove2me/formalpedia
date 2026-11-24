-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_StarPf_stStar
-- name    : GlobalTheory.CompanionTheory.RgFl.StarPf.stStar
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:49.363969+00:00
-- url     : https://prove2.me/theorems/6268aa66-7d00-42de-aa0b-b9d344bc3c74
-- title:
--   Star Pf: st Star
-- statement:
--   The Star Pf construction uses the st Star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/StatementStar.lean#L63-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/StatementStar.lean#L63-L144

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_SmallPI
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StatementStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl GlobalTheory.CompanionTheory.RgFl.StarPf

theorem GlobalTheory.CompanionTheory.RgFl.StarPf.stStar : StStar := by sorry
