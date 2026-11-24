-- Prove2me | Theorems.Thm_GlobalTheory_weilSt_of_parts
-- name    : GlobalTheory.weilSt_of_parts
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:05.991741+00:00
-- url     : https://prove2.me/theorems/8efc7172-0b09-4d84-94a7-e8f5635a0161
-- title:
--   Global Theory: weil St of parts
-- statement:
--   The Global Theory construction uses the weil St of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilStOfParts.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilStOfParts.lean#L9-L12

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilStOfParts
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

theorem GlobalTheory.weilSt_of_parts :
    (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (x y : T ⟶ P.A), x ^ k = 1 → y ^ k = 1 → ∃! c : Γ(T.left, ⊤)ˣ, WeilIs P.A P.L k x y c) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (x x' y : T ⟶ P.A) (c c' : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k x' y c' → WeilIs P.A P.L k (x * x') y (c * c')) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c)) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (l : ℕ) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), IsUnit ((k * l : ℕ) : Γ(T.left, ⊤)) → x ^ (k * l) = 1 → y ^ k = 1 → (WeilIs P.A P.L (k * l) x y c ↔ WeilIs P.A P.L k (x ^ l) y c)) → WeilSt := by sorry
