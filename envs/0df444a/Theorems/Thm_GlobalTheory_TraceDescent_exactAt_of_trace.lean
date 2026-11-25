-- Prove2me | Theorems.Thm_GlobalTheory_TraceDescent_exactAt_of_trace
-- name    : GlobalTheory.TraceDescent.exactAt_of_trace
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:50:00.733187+00:00
-- url     : https://prove2.me/theorems/38c109b8-d497-4e7d-9556-bfb8c08a1f89
-- title:
--   Trace Descent: exact At of trace
-- statement:
--   The Trace Descent construction uses the exact At of trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExactAtSectionCubeOfMulPullback.lean#L25-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExactAtSectionCubeOfMulPullback.lean#L25-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExactAtSectionCubeOfMulPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory
noncomputable section
open GlobalTheory GlobalTheory.TraceDescent
open GlobalTheory.AbLaw.PowVanish

theorem GlobalTheory.TraceDescent.exactAt_of_trace {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (A B : GlobalTheory.Cube.{0} κ R)
    (φ : ∀ s, A.obj s →+ B.obj s) (T : ∀ s, B.obj s →+ B.obj s)
    (hφ : ∀ {s t : Finset κ} (h : s ⊆ t) x, φ t (Cube.res A h x) = Cube.res B h (φ s x))
    (hT : ∀ {s t : Finset κ} (h : s ⊆ t) x, T t (Cube.res B h x) = Cube.res B h (T s x))
    (inj : ∀ s, Function.Injective (φ s)) (n : ℕ) (hn : IsUnit (n : R))
    (himg : ∀ s y, ∃ x, φ s x = T s y) (htr : ∀ s x, T s (φ s x) = n • φ s x) (p : ℕ)
    (H : (cubeComplex B).ExactAt p) : (cubeComplex A).ExactAt p := by sorry
