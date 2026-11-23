-- Prove2me | Theorems.Thm_GlobalTheory_InducedPBW_eq_on_degLt
-- name    : GlobalTheory.InducedPBW.eq_on_degLt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:00.380807+00:00
-- url     : https://prove2.me/theorems/6ea068e2-e19d-4168-b912-390061dba332
-- title:
--   Induced PBW: eq on deg Lt
-- statement:
--   The Induced PBW construction uses the eq on deg Lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L41-L46

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

theorem GlobalTheory.InducedPBW.eq_on_degLt {W : Type*} [AddCommGroup W] [Module R W] {n : ℕ}
    (f f' : (MvPolynomial ι R ⊗[R] V) →ₗ[R] W)
    (h : ∀ α v, α.degree < n → f (zv α v) = f' (zv α v)) : ∀ m ∈ degLt R ι V n, f m = f' m := by sorry
