-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDescent_formallySmooth_of_faithfullyFlat
-- name    : GlobalTheory.SmoothDescent.formallySmooth_of_faithfullyFlat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:15:33.863407+00:00
-- url     : https://prove2.me/theorems/cb4324a5-fa4a-45d0-bd6d-5347a3df970a
-- title:
--   Smooth Descent: formally Smooth of faithfully Flat
-- statement:
--   The Smooth Descent construction uses the formally Smooth of faithfully Flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionDescendsEtaleCover.lean#L69-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionDescendsEtaleCover.lean#L69-L132

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

theorem GlobalTheory.SmoothDescent.formallySmooth_of_faithfullyFlat (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsNoetherianRing R] [IsLocalRing A]
    [Algebra.EssFiniteType R A] [Algebra.EssFiniteType A B] [Module.FaithfullyFlat A B]
    [Algebra.FormallyEtale A B] [Algebra.FormallySmooth R B] : Algebra.FormallySmooth R A := by sorry
