-- Prove2me | Theorems.Thm_GlobalTheory_SS_DefectZero_isSmoothAt_of_ker
-- name    : GlobalTheory.SS.DefectZero.isSmoothAt_of_ker
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:33:54.606431+00:00
-- url     : https://prove2.me/theorems/a2f4dbc5-d48b-43be-86a1-eb69fc850335
-- title:
--   Defect Zero: is Smooth At of ker
-- statement:
--   The Defect Zero construction uses the is Smooth At of ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L86-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L86-L127

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open TensorProduct KaehlerDifferential
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.DefectZero

theorem GlobalTheory.SS.DefectZero.isSmoothAt_of_ker (R C B : Type) [CommRing R] [IsRegularRing R] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra.FinitePresentation R C] [Algebra R B] (ψ : C →ₐ[R] B)
    (hs : Function.Surjective ψ) (x : Ideal B) [x.IsPrime] (x' : Ideal C) [x'.IsPrime]
    (hx : x' = x.comap ψ.toRingHom) [Algebra.IsSmoothAt R x'] (q : Ideal C) [q.IsPrime]
    (hq : q ≤ x') (h : ∀ c, ψ c = 0 → ∃ u ∉ q, u * c = 0) : Algebra.IsSmoothAt R x := by sorry
