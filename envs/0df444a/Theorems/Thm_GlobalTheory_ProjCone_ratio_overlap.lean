-- Prove2me | Theorems.Thm_GlobalTheory_ProjCone_ratio_overlap
-- name    : GlobalTheory.ProjCone.ratio_overlap
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:26:29.601796+00:00
-- url     : https://prove2.me/theorems/ebc25725-a25f-56fb-be90-9527a0a77ed7
-- title:
--   Proj Cone: ratio overlap
-- statement:
--   The Proj Cone construction uses the ratio overlap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L280-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L280-L309

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

theorem GlobalTheory.ProjCone.ratio_overlap (c c' q : σ) :
    resG _ (inf_le_left : chart I c ⊓ chart I c' ≤ _) (ratio I c q) *
      resG _ (inf_le_right : chart I c ⊓ chart I c' ≤ _) (ratio I c' c) =
    resG _ (inf_le_right : chart I c ⊓ chart I c' ≤ _) (ratio I c' q) := by sorry
