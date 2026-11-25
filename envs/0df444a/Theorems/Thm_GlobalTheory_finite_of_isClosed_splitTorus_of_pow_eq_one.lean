-- Prove2me | Theorems.Thm_GlobalTheory_finite_of_isClosed_splitTorus_of_pow_eq_one
-- name    : GlobalTheory.finite_of_isClosed_splitTorus_of_pow_eq_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:16.426807+00:00
-- url     : https://prove2.me/theorems/5401cfb0-9b70-4827-859b-defa577115ef
-- title:
--   Global Theory: finite of is Closed split Torus of pow eq one
-- statement:
--   The Global Theory construction uses the finite of is Closed split Torus of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FiniteOfIsClosedSplitTorusOfPowEqOne.lean#L139-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FiniteOfIsClosedSplitTorusOfPowEqOne.lean#L139-L159

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedSplitTorusOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open GlobalTheory
variable {k : Type} [Field k] {X : Type} [AddCommGroup X]
attribute [local instance] zuAlgebra
open scoped AlgebraMonoidAlgebra

theorem GlobalTheory.finite_of_isClosed_splitTorus_of_pow_eq_one :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
      [Module.Finite ℤ X] (n : ℕ), n.Prime → (n : k) ≠ 0 →
      ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X))
        (Z : Set (splitTorus (Sp k) X).left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) →
        (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C := by sorry
