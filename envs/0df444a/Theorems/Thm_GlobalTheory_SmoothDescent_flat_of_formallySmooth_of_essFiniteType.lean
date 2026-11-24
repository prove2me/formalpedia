-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDescent_flat_of_formallySmooth_of_essFiniteType
-- name    : GlobalTheory.SmoothDescent.flat_of_formallySmooth_of_essFiniteType
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:15:29.757646+00:00
-- url     : https://prove2.me/theorems/2da8af08-5b10-4e4d-85de-1f9ace8e1c1b
-- title:
--   Smooth Descent: flat of formally Smooth of ess Finite Type
-- statement:
--   The Smooth Descent construction uses the flat of formally Smooth of ess Finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionDescendsEtaleCover.lean#L16-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionDescendsEtaleCover.lean#L16-L39

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

theorem GlobalTheory.SmoothDescent.flat_of_formallySmooth_of_essFiniteType (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    [IsNoetherianRing R] [Algebra.EssFiniteType R B] [Algebra.FormallySmooth R B] :
    Module.Flat R B := by sorry
