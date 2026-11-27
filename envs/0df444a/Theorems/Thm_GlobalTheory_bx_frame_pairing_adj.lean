-- Prove2me | Theorems.Thm_GlobalTheory_bx_frame_pairing_adj
-- name    : GlobalTheory.bx_frame_pairing_adj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:47:35.751033+00:00
-- url     : https://prove2.me/theorems/ddd43f4f-fe61-4db9-a0b9-e02fe2f55e3d
-- title:
--   Global Theory: bx frame pairing adj
-- statement:
--   The Global Theory construction uses the bx frame pairing adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TransportRightSmulFrame.lean#L123-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TransportRightSmulFrame.lean#L123-L170

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TransportRightSmulFrame
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

theorem GlobalTheory.bx_frame_pairing_adj :
  (∀ {R₀ : Type} [CommRing R₀] (B : BX R₀) (b : ∀ R x y, B.P R x y) (t₁ t₂ : ∀ R : LAlg R₀, B.G R → B.G R → B.G R → (R : Type)ˣ),
    (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R x x' y) (b R (x + x') y)) →
    (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R x y y') (b R x (y + y'))) →
    (∀ R (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ), B.IsPairing (N + 1) x y z ↔ (N + 1) • x = 0 ∧ (N + 1) • y = 0 ∧
      z = (t₁ R 0 0 y * ∏ k ∈ Finset.range N, t₁ R ((k + 1) • x) x y) / (t₂ R x 0 0 * ∏ k ∈ Finset.range N, t₂ R x ((k + 1) • y) y)) ∧
    ∀ (O : LAlg R₀) (a a' : OEnd B O) (u : ∀ {R : LAlg R₀}, LHom O R → B.G R → B.G R → (R : Type)ˣ),
      (∀ {R : LAlg R₀} (s : LHom O R) x x' y, u s (x + x') y * t₁ R x x' (a'.f s y) = t₁ R (a.f s x) (a.f s x') y * (u s x y * u s x' y)) →
      (∀ {R : LAlg R₀} (s : LHom O R) x y y', u s x (y + y') * t₂ R x (a'.f s y) (a'.f s y') = t₂ R (a.f s x) y y' * (u s x y * u s x y')) →
      ∃ A : OAdj B O, A.a = a ∧ A.ab = a') := by sorry
