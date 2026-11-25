-- Prove2me | Theorems.Thm_GlobalTheory_ProjCone_dehom_eq_zero_of_mem
-- name    : GlobalTheory.ProjCone.dehom_eq_zero_of_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:15:35.450559+00:00
-- url     : https://prove2.me/theorems/f17b0ac8-c244-504f-9558-841f25a49610
-- title:
--   Proj Cone: dehom eq zero of mem
-- statement:
--   The Proj Cone construction uses the dehom eq zero of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L113-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L113-L120

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
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.ProjCone.dehom_eq_zero_of_mem (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ)) (c : σ) {F : MvPolynomial σ ℂ}
    (hF : F ∈ I) : dehom I c F = 0 := by sorry
