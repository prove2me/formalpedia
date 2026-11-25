-- Prove2me | Theorems.Thm_GlobalTheory_ProjCone_isIntegral_proj
-- name    : GlobalTheory.ProjCone.isIntegral_proj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:22:34.000642+00:00
-- url     : https://prove2.me/theorems/003c42a8-9832-538b-b69d-31fbd6846e98
-- title:
--   Proj Cone: is Integral proj
-- statement:
--   The Proj Cone construction uses the is Integral proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L13-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L13-L37

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

theorem GlobalTheory.ProjCone.isIntegral_proj {A : Type} [CommRing A] [IsDomain A] [Algebra ℂ A] (𝒜 : ℕ → Submodule ℂ A) [GradedAlgebra 𝒜]
    {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) (hm : 0 < m) (hf0 : f ≠ 0) : IsIntegral (Proj 𝒜) := by sorry
