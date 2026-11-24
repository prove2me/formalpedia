-- Prove2me | Theorems.Thm_GlobalTheory_InducedPBW_comm_high
-- name    : GlobalTheory.InducedPBW.comm_high
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:16:01.33062+00:00
-- url     : https://prove2.me/theorems/e005645d-8259-4e93-b8fb-d75226f2fadc
-- title:
--   Induced PBW: comm high
-- statement:
--   The Induced PBW construction uses the comm high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L281-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L281-L295

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

theorem GlobalTheory.InducedPBW.comm_high (i : ι) (J : ι →₀ ℕ) (hJ : ∀ j ∈ J.support, i ≤ j) (x : g)
    (hx : ∀ j, j ≤ i → c j x = 0) (v : V) :
    rho c δ x (rho c δ (e i) (zv J v)) =
      rho c δ (e i) (rho c δ x (zv J v)) + rho c δ ⁅x, e i⁆ (zv J v) := by sorry
