-- Prove2me | Theorems.Thm_GlobalTheory_ProjCone_awayEquiv_dehom
-- name    : GlobalTheory.ProjCone.awayEquiv_dehom
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:27:47.228141+00:00
-- url     : https://prove2.me/theorems/01320831-de2d-47db-994a-7272e19de0c3
-- title:
--   Proj Cone: away Equiv dehom
-- statement:
--   The Proj Cone construction uses the away Equiv dehom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L256-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L256-L271

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

theorem GlobalTheory.ProjCone.awayEquiv_dehom (c : σ) (F : MvPolynomial σ ℂ) :
    awayEquiv I c (dehom I c F) = eval₂ (RingHom.comp ((toSpecC I).appLE ⊤ (chart I c) le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) (ratio I c) F := by sorry
