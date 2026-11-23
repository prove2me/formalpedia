-- Prove2me | Theorems.Thm_GlobalTheory_T_symmetric_lift_odd_order_exists_unique
-- name    : GlobalTheory.T.symmetric_lift_odd_order_exists_unique
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:31.049698+00:00
-- url     : https://prove2.me/theorems/7854ac81-a8b1-4e35-af18-9335d57cc983
-- title:
--   T: symmetric lift odd order exists unique
-- statement:
--   The T construction uses the symmetric lift odd order exists unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SymmetricLiftOddOrderExistsUniqueStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SymmetricLiftOddOrderExistsUniqueStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUniqueStatement
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

theorem GlobalTheory.T.symmetric_lift_odd_order_exists_unique : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ nu : LB.Gen (negLB P.A P.L k T), nu.IsGen) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ), Odd k → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 → (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L k (overRes V), SymLift P.A P.L k k (overResι V ≫ x) θ) ∧ ∀ θ θ' : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ → SymLift P.A P.L k k x θ' → LB.Gen.Corr P.L _ _ _ _ θ.φ θ'.φ) ∧ SymLiftSt := by sorry
