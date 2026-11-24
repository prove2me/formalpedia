-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDescent_formallySmooth_of_flat_of_formallyUnramified
-- name    : GlobalTheory.SmoothDescent.formallySmooth_of_flat_of_formallyUnramified
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:15:42.592068+00:00
-- url     : https://prove2.me/theorems/bdcb5eff-1406-431f-a05f-8c341e2dd121
-- title:
--   Smooth Descent: formally Smooth of flat of formally Unramified
-- statement:
--   The Smooth Descent construction uses the formally Smooth of flat of formally Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionDescendsEtaleCover.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionDescendsEtaleCover.lean#L41-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionDescendsEtaleCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SmoothDescent
open TensorProduct KaehlerDifferential

theorem GlobalTheory.SmoothDescent.formallySmooth_of_flat_of_formallyUnramified (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]
    [Algebra.EssFiniteType R A] [Module.Flat R A] [Algebra.FormallyUnramified R A] :
    Algebra.FormallySmooth R A := by sorry
