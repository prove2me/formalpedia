-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LowKType_orthCyc
-- name    : GlobalTheory.CompanionTheory.LowKType.orthCyc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:03.010879+00:00
-- url     : https://prove2.me/theorems/d8198242-b95a-4c41-840a-b0cddd11fc64
-- title:
--   Low KType: orth Cyc
-- statement:
--   The Low KType construction uses the orth Cyc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OrthCycCycStable.lean#L18-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OrthCycCycStable.lean#L18-L54

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OrthCycCycStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LowKType
open CompanionTheory.D.LK CompanionTheory.D.DSIC Formalism.REAL

theorem GlobalTheory.CompanionTheory.LowKType.orthCyc : CompanionTheory.D.LK.OrthCyc := by sorry
