-- Prove2me | Theorems.Thm_GlobalTheory_sq_eq_det_aeval_of_sq
-- name    : GlobalTheory.sq_eq_det_aeval_of_sq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:51:31.054778+00:00
-- url     : https://prove2.me/theorems/c00661ab-ad31-4fae-a655-09db6254b82f
-- title:
--   Global Theory: sq eq det aeval of sq
-- statement:
--   The Global Theory construction uses the sq eq det aeval of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSqAddSubDvd.lean#L149-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSqAddSubDvd.lean#L149-L168

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSqAddSubDvd
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory

theorem GlobalTheory.sq_eq_det_aeval_of_sq : ∀ (l : ℕ) [Fact l.Prime] (m g : ℕ) (U : Matrix (Fin m) (Fin m) ℤ_[l]) (D : Polynomial ℤ → ℚ), (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous g ∧ ∀ a : Fin r → ℤ, D (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) → (∀ G, ((D (G ^ 2) : ℚ) : ℚ_[l]) = ((Polynomial.aeval U G).det : ℤ_[l])) → (∀ F H, Polynomial.aeval U H = 0 → D (F + H) = D F) → ∀ F, ((D F ^ 2 : ℚ) : ℚ_[l]) = ((Polynomial.aeval U F).det : ℤ_[l]) := by sorry
