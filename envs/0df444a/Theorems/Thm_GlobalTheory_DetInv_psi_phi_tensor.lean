-- Prove2me | Theorems.Thm_GlobalTheory_DetInv_psi_phi_tensor
-- name    : GlobalTheory.DetInv.psi_phi_tensor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:35.986583+00:00
-- url     : https://prove2.me/theorems/35ad8cb8-86a2-5be7-8d82-10323f10eb21
-- title:
--   Det Inv: psi phi tensor
-- statement:
--   The Det Inv construction uses the psi phi tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusOfPadic.lean#L57-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusOfPadic.lean#L57-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IotaScalarOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusOfPadic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
open GlobalTheory GlobalTheory.DetInv
open PsiPhi

theorem GlobalTheory.DetInv.psi_phi_tensor : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ],
    (∀ c : ℤ_[p], phiInv p O (ofPadic p O c) = ofPadic p O c) ∧ Function.Bijective (phiInv p O) ∧
    ∃ ψ φ : RL p O Λ →+* RL p O Λ, IsPsi ψ ∧
      (∀ (a : Ainf p O) (l : Λ), φ (a ⊗ₜ l) = WittVector.frobenius a ⊗ₜ l) ∧
      (∀ r, φ (ψ r) = r) ∧ ∀ r, ψ (φ r) = r := by sorry
