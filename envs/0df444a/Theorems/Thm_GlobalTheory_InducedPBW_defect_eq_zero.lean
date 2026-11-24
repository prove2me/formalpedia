-- Prove2me | Theorems.Thm_GlobalTheory_InducedPBW_defect_eq_zero
-- name    : GlobalTheory.InducedPBW.defect_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:15:17.809587+00:00
-- url     : https://prove2.me/theorems/ea73b474-e219-4395-9467-45b39dab7667
-- title:
--   Induced PBW: defect eq zero
-- statement:
--   The Induced PBW construction uses the defect eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L350-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L350-L409

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.InducedPBW
variable {R : Type*} [CommRing R] {ι : Type*} {V : Type*} [AddCommGroup V] [Module R V]
variable {g : Type*} [LieRing g] [LieAlgebra R g]
variable [Fintype ι] [LinearOrder ι] (e : ι → g) (c : ι → g →ₗ[R] R) (act : g →ₗ[R] Module.End R V)
variable {e c act} {δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)}
  (hce : ∀ i j, c i (e j) = if i = j then 1 else 0)
include hce
variable (hf : step e c act δ = δ)
include hf

theorem GlobalTheory.InducedPBW.defect_eq_zero (hp : Pres δ)
    (hK : ∀ x y, (∀ j, c j x = 0) → (∀ j, c j y = 0) → ∀ j, c j ⁅x, y⁆ = 0)
    (hact : ∀ x y, (∀ j, c j x = 0) → (∀ j, c j y = 0) →
      act ⁅x, y⁆ = act x * act y - act y * act x) (n : ℕ) :
    ∀ x y, ∀ m ∈ degLt R ι V n, defect c δ m x y = 0 := by sorry
