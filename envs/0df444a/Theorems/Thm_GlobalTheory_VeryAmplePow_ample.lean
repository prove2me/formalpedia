-- Prove2me | Theorems.Thm_GlobalTheory_VeryAmplePow_ample
-- name    : GlobalTheory.VeryAmplePow.ample
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:49:32.923546+00:00
-- url     : https://prove2.me/theorems/9103c8e7-3641-48f3-bad0-3453558416f3
-- title:
--   Very Ample Pow: ample
-- statement:
--   The Very Ample Pow construction uses the ample property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L315-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L315-L412

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
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
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem GlobalTheory.VeryAmplePow.ample : (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → ∀ U : S.Opens, IsAffineOpen U → ∃ (m : ℕ) (b : Fin (m + 1) → LB.Sec (LPow P.A P.L n (overRes (T := baseOver S) U))), ∀ (T' : Over S) [IsAffine T'.left] (h : T' ⟶ overRes (T := baseOver S) U) (b' : Fin (m + 1) → LB.Sec (LPow P.A P.L n T')), (∀ i, IsPullSec P.A P.L n (h ▷ P.A) (whiskerRight_snd h P.A) (b i) (b' i)) → Submodule.span Γ(T'.left, ⊤) (Set.range fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n T')) = ⊤) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 2 ≤ n → ∀ x : Over.mk t ⟶ P.A, ∃ (s : LB.Sec (LPow P.A P.L n (Over.mk t))) (τ : LB.Gen (LB.LinComb P.L (Y := (Over.mk t).left) (K := Fin 1) (fun _ => x.left) (fun _ => (n : ℤ)))) (v : Γ((Over.mk t).left, ⊤)), τ.IsGen ∧ IsValueAt P.A P.L n s x τ v ∧ IsUnit v) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 3 ≤ n → ∀ (T : Over S) [IsLocallyNoetherian T.left] (x y : T ⟶ P.A) (τx : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => (n : ℤ)))) (τy : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => y.left) (fun _ => (n : ℤ)))), τx.IsGen → τy.IsGen → (∀ (T' : Over S) [IsAffine T'.left] (h : T' ⟶ T) (s : LB.Sec (LPow P.A P.L n T')) (vx vy : Γ(T'.left, ⊤)), IsValueAt P.A P.L n s (h ≫ x) (LB.pullGen P.L _ _ τx h.left) vx → IsValueAt P.A P.L n s (h ≫ y) (LB.pullGen P.L _ _ τy h.left) vy → vx = vy) → x = y) → AmpleSt := by sorry
