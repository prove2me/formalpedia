-- Prove2me | Theorems.Thm_GlobalTheory_ProjCone_awayEquiv_dehom_C
-- name    : GlobalTheory.ProjCone.awayEquiv_dehom_C
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:15:34.976197+00:00
-- url     : https://prove2.me/theorems/4627bb88-8f09-5c79-996d-0f45f263eb6e
-- title:
--   Proj Cone: away Equiv dehom C
-- statement:
--   The Proj Cone construction uses the away Equiv dehom C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L228-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L228-L254

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

theorem GlobalTheory.ProjCone.awayEquiv_dehom_C (c : σ) (a : ℂ) : awayEquiv I c (dehom I c (C a)) = constFn (toSpecC I) (chart I c) a := by sorry
