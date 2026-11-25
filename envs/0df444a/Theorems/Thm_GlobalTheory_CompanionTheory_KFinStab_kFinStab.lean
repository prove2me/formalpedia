-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KFinStab_kFinStab
-- name    : GlobalTheory.CompanionTheory.KFinStab.kFinStab
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:21:21.009379+00:00
-- url     : https://prove2.me/theorems/1d7af697-53a5-4f96-915e-49827c7dc13a
-- title:
--   KFin Stab: k Fin Stab
-- statement:
--   The KFin Stab construction uses the k Fin Stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MemUJsetOfMemKset.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MemUJsetOfMemKset.lean#L11-L12

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KsetSubset
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemUJsetOfMemKset
import Theorems.Thm_UpperTheory_Reformulated_B_Gc1_kFinStab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open PI.UpqRep (UJset Kset IsKFin IsKStableOn)
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KFinStab

theorem GlobalTheory.CompanionTheory.KFinStab.kFinStab : CompanionTheory.D.DSIC.KFinStab := by sorry
