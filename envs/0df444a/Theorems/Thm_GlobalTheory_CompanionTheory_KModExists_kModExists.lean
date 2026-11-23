-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KModExists_kModExists
-- name    : GlobalTheory.CompanionTheory.KModExists.kModExists
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:03.452245+00:00
-- url     : https://prove2.me/theorems/962e11d8-fb53-418b-a816-6ab95309df78
-- title:
--   KMod Exists: k Mod Exists
-- statement:
--   The KMod Exists construction uses the k Mod Exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CompactFiniteAdelesAwayPBoundedDenominators.lean#L41-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CompactFiniteAdelesAwayPBoundedDenominators.lean#L41-L85

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CompactFiniteAdelesAwayPBoundedDenominators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KModExists
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open PI.UpqRep (IsKFin IsKTypeOf IsKStableOn)
open CompanionTheory.D.DSIC

theorem GlobalTheory.CompanionTheory.KModExists.kModExists (h1 : SmMod) (h2 : KFinSm) (h3 : KFinStab) (h4 : StabLink) (h5 : HWofType) (h6 : TypeOfHW) :
    CompanionTheory.D.LK.KModExists := by sorry
