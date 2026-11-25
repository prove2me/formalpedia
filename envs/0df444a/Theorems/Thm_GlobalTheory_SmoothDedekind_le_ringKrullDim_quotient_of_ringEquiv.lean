-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDedekind_le_ringKrullDim_quotient_of_ringEquiv
-- name    : GlobalTheory.SmoothDedekind.le_ringKrullDim_quotient_of_ringEquiv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:11:19.314653+00:00
-- url     : https://prove2.me/theorems/4830ee57-b32c-575c-aa1b-dc9e907164f4
-- title:
--   Smooth Dedekind: le ring Krull Dim quotient of ring Equiv
-- statement:
--   The Smooth Dedekind construction uses the le ring Krull Dim quotient of ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfFlatDedekindTangentLe.lean#L96-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfFlatDedekindTangentLe.lean#L96-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfFlatDedekindTangentLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.SmoothDedekind
open GlobalTheory.SmoothTangent IsLocalRing

theorem GlobalTheory.SmoothDedekind.le_ringKrullDim_quotient_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    {d : WithBot ℕ∞} (hd : ∀ q ∈ minimalPrimes S, d ≤ ringKrullDim (S ⧸ q)) :
    ∀ p ∈ minimalPrimes R, d ≤ ringKrullDim (R ⧸ p) := by sorry
