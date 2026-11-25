-- Prove2me | Theorems.Thm_GlobalTheory_ProjCone_ringKrullDim_away_le
-- name    : GlobalTheory.ProjCone.ringKrullDim_away_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:15:47.679018+00:00
-- url     : https://prove2.me/theorems/e2e7f867-7676-5ec7-9fc7-2ef2c4e7db17
-- title:
--   Proj Cone: ring Krull Dim away le
-- statement:
--   The Proj Cone construction uses the ring Krull Dim away le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L151-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L151-L178

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

theorem GlobalTheory.ProjCone.ringKrullDim_away_le (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ)) (hP : I.IsPrime) (c : σ) (g : ℕ)
    (hg : ringKrullDim (MvPolynomial σ ℂ ⧸ I) ≤ (g + 1 : ℕ)) :
    ringKrullDim (HomogeneousLocalization.Away (quotGrading I) (coord I c)) ≤ g := by sorry
