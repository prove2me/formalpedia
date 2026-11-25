-- Prove2me | Theorems.Thm_GlobalTheory_tateBasis_gram
-- name    : GlobalTheory.tateBasis_gram
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:40:31.827478+00:00
-- url     : https://prove2.me/theorems/e84aeecf-10c4-5fd4-8570-e49906595fe2
-- title:
--   Global Theory: tate Basis gram
-- statement:
--   The Global Theory construction uses the tate Basis gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TateBasisGram.lean#L80-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TateBasisGram.lean#L80-L157

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.tateBasis_gram :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} (B : BX R₀) (Tw : ATowerL R₀ p) [IsDomain (Tw.O : Type)] [Algebra ℤ_[p] (Tw.O : Type)],
    (∀ n, RingHom.ker (Tw.q n).1 = Ideal.span {((p : ℕ) : (Tw.O : Type)) ^ (n + 1)}) →
    (∀ n, IsPrimitiveRoot (Tw.ζ n) (p ^ (n + 1))) → (∀ n, Tw.ζ (n + 1) ^ p = Tw.ζ n) →
    ∀ τ : Ix g → ℕ → B.G Tw.O, (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    (∀ x : B.G Tw.O, p • x = 0 → ∃! t : Ix g → ZMod p, x = ptOf B τ t) →
    (∀ x : B.G Tw.O, p • x = 0 → (∀ y : B.G Tw.O, p • y = 0 → B.IsPairing p x y 1) → x = 0) →
    ∃ E : Matrix (Ix g) (Ix g) ℤ_[p], (Eᵀ = -E ∧ ∀ i, E i i = 0) ∧ IsUnit E.det ∧
      ∀ i j n, B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ (PadicInt.toZModPow (n + 1) (E i j)).val)) := by sorry
