-- Prove2me | Theorems.Thm_GlobalTheory_T_thetaObject_comparison_maps_cocycle
-- name    : GlobalTheory.T.thetaObject_comparison_maps_cocycle
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:00:15.539797+00:00
-- url     : https://prove2.me/theorems/4fc66ac3-1719-45ed-a87d-ab2227a69eae
-- title:
--   T: theta Object comparison maps cocycle
-- statement:
--   The T construction uses the theta Object comparison maps cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaObjectComparisonMapsCocycleStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaObjectComparisonMapsCocycleStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaObjectComparisonMapsCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaObjectComparisonMapsCocycleStatement
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
open GlobalTheory.ZM
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.thetaObject_comparison_maps_cocycle : (∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s), f ≫ s = s' → ∃ t' : TObj g k J b s', TMap t' t f) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (β : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (I : Type) (U : I → S.Opens) (t : ∀ i, TObj g k J β ((U i).ι ≫ s)) (u : ∀ i j, TObj g k J β ((U i ⊓ U j).ι ≫ s)) (a : ∀ i j, (u i j).A.left ⟶ (t i).A.left) (b : ∀ i j, (u i j).A.left ⟶ (t j).A.left), (∀ i j, IsGrpPullback (u i j).A (t i).A (S.homOfLE inf_le_left) (a i j) ∧ LBIso (u i j).L ((t i).L.pull (a i j)) ∧ ∀ l, ((u i j).pt l).left ≫ a i j = S.homOfLE inf_le_left ≫ ((t i).pt l).left) → (∀ i j, IsGrpPullback (u i j).A (t j).A (S.homOfLE inf_le_right) (b i j) ∧ LBIso (u i j).L ((t j).L.pull (b i j)) ∧ ∀ l, ((u i j).pt l).left ≫ b i j = S.homOfLE inf_le_right ≫ ((t j).pt l).left) → (∀ (T : Scheme.{0}) (i : I) (f : T ⟶ (U i).toScheme) (u : TObj g k J β (f ≫ (U i).ι ≫ s)) (φ φ' : u.A.left ⟶ (t i).A.left), IsOpenImmersion f → IsGrpPullback u.A (t i).A f φ → IsGrpPullback u.A (t i).A f φ' → LBIso u.L ((t i).L.pull φ) → LBIso u.L ((t i).L.pull φ') → (∀ a, (u.pt a).left ≫ φ = (u.pt a).left ≫ φ') → φ = φ') → ∀ i j k (T : Scheme.{0}) (x : T ⟶ (u i j).A.left) (y : T ⟶ (u j k).A.left) (z : T ⟶ (u i k).A.left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k := by sorry
