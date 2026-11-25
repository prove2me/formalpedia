-- Prove2me | Theorems.Thm_GlobalTheory_ProjCone_val_dehom_of_isHomogeneous
-- name    : GlobalTheory.ProjCone.val_dehom_of_isHomogeneous
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:33:18.307026+00:00
-- url     : https://prove2.me/theorems/96c5bfe5-313b-5d3e-9437-16388b19c91f
-- title:
--   Proj Cone: val dehom of is Homogeneous
-- statement:
--   The Proj Cone construction uses the val dehom of is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L92-L96

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.ProjCone
variable {σ : Type} (I : Ideal (MvPolynomial σ ℂ)) [GradedAlgebra (quotGrading I)]

theorem GlobalTheory.ProjCone.val_dehom_of_isHomogeneous (c : σ) {f : MvPolynomial σ ℂ} {n : ℕ} (hf : f.IsHomogeneous n) :
    (dehom I c f).val = Localization.mk (Ideal.Quotient.mk I f) 1 * invCoord I c ^ n := by sorry
