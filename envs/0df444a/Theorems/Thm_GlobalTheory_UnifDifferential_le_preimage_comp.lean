-- Prove2me | Theorems.Thm_GlobalTheory_UnifDifferential_le_preimage_comp
-- name    : GlobalTheory.UnifDifferential.le_preimage_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:57.539167+00:00
-- url     : https://prove2.me/theorems/3197f632-918e-41b8-8cba-cb3404f5226c
-- title:
--   Unif Differential: le preimage comp
-- statement:
--   The Unif Differential construction uses the le preimage comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SubsingletonPrimeSpectrum.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SubsingletonPrimeSpectrum.lean#L46-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (sp IsTan fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.SqZero
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.UnifDifferential
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))}
  {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']

theorem GlobalTheory.UnifDifferential.le_preimage_comp (φ : S →ₐ[R] S') (y : sp (R₀ := R) S ⟶ A) (y' : sp (R₀ := R) S' ⟶ A)
    (e : y' = Chart.spMap φ ≫ y) (U : A.left.Opens) (h : ⊤ ≤ y.left ⁻¹ᵁ U) :
    ⊤ ≤ y'.left ⁻¹ᵁ U := by sorry
