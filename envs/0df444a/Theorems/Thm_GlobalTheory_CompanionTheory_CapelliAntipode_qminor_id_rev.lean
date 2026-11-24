-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAntipode_qminor_id_rev
-- name    : GlobalTheory.CompanionTheory.CapelliAntipode.qminor_id_rev
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:12.475305+00:00
-- url     : https://prove2.me/theorems/287dec48-ff9b-4af5-b3f3-a2edd0cb6534
-- title:
--   Capelli Antipode: qminor id rev
-- statement:
--   The Capelli Antipode construction uses the qminor id rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetOppositeNeg.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetOppositeNeg.lean#L52-L62

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliAntipode

theorem GlobalTheory.CompanionTheory.CapelliAntipode.qminor_id_rev {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (w : ℂ) :
    qminor X id (id ∘ (Fin.revPerm : Equiv.Perm (Fin n))) w =
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) *
        ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
          (List.ofFn fun j : Fin n => Tm X (w - ((j : ℕ) : ℂ)) (σ j.rev) j.rev).prod := by sorry
