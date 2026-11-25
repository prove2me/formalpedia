-- Prove2me | Theorems.Thm_GlobalTheory_UnifEigenRank_finrank_eigenspace_of_lieMult
-- name    : GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:40:17.998829+00:00
-- url     : https://prove2.me/theorems/57df7f37-7d5e-416f-a8b0-bb1b6c81d992
-- title:
--   Unif Eigen Rank: finrank eigenspace of lie Mult
-- statement:
--   The Unif Eigen Rank construction uses the finrank eigenspace of lie Mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FinrankEigenspaceOfLieMultiplicity.lean#L35-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FinrankEigenspaceOfLieMultiplicity.lean#L35-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLieBasisOfHolUnif
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FinrankEigenspaceOfLieMultiplicity
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory.UnifLieBasis
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD isTan_iff isLieComb_iff isTan_scale)

theorem GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (O : Type) [CommRing O] (act : OAct O P₀.A) (F : O → Module.End ℂ (Fin P₀.g → ℂ)), (∀ a z, u.ex (F a z) = u.ex z ≫ act.act a) → ∀ (τ : O →+* ℂ) (n : ℕ), LieMult act (𝟙 _) τ n → Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = n := by sorry
