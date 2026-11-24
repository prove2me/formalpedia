-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAntipode_unop_term
-- name    : GlobalTheory.CompanionTheory.CapelliAntipode.unop_term
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:09.610652+00:00
-- url     : https://prove2.me/theorems/ed2dcdc5-b9c2-4ab0-a276-cdb91cac8583
-- title:
--   Capelli Antipode: unop term
-- statement:
--   The Capelli Antipode construction uses the unop term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetOppositeNeg.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetOppositeNeg.lean#L40-L50

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

theorem GlobalTheory.CompanionTheory.CapelliAntipode.unop_term {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (v : ℂ)
    (σ : Equiv.Perm (Fin n)) :
    MulOpposite.unop ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Aᵐᵒᵖ) *
        (List.ofFn fun k : Fin n =>
          Tm (fun i j => MulOpposite.op (-X i j)) (v - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod) =
      ((-1 : ℂ) ^ n) • ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
        (List.ofFn fun j : Fin n =>
          Tm X (((n : ℂ) - 1 - v) - ((j : ℕ) : ℂ)) (σ j.rev) j.rev).prod) := by sorry
