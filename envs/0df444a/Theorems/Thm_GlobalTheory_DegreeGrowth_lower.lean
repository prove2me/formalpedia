-- Prove2me | Theorems.Thm_GlobalTheory_DegreeGrowth_lower
-- name    : GlobalTheory.DegreeGrowth.lower
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:44:01.548834+00:00
-- url     : https://prove2.me/theorems/0d864c77-20a5-42e1-8e85-74c50c90415d
-- title:
--   Degree Growth: lower
-- statement:
--   The Degree Growth construction uses the lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankTotalDegreeImageGrowth.lean#L146-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankTotalDegreeImageGrowth.lean#L146-L187

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.DegreeGrowth
variable {K B : Type} [Field K] [CommRing B] [Algebra K B]

theorem GlobalTheory.DegreeGrowth.lower {s m : ℕ} (φ : MvPolynomial (Fin s) K →ₐ[K] B) (hφ : Function.Injective φ)
    (r : Fin m → B)
    (hr : Function.Surjective (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B)) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ t : ℕ,
      t ^ s ≤ c * Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map
        (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) := by sorry
