-- Prove2me | Theorems.Thm_GlobalTheory_DiagBlock_kill_det_pow
-- name    : GlobalTheory.DiagBlock.kill_det_pow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:44:19.64286+00:00
-- url     : https://prove2.me/theorems/b03fba87-5c17-411c-94e7-a14ec8cb1358
-- title:
--   Diag Block: kill det pow
-- statement:
--   The Diag Block construction uses the kill det pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L112-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L112-L142

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock

theorem GlobalTheory.DiagBlock.kill_det_pow {R : Type} [CommRing R] {σ : Type} (S : σ → Prop) [DecidablePred S]
    {n0 n : ℕ} (hn : n0 ≤ n) (f : Fin n → Fin n → σ)
    (hf : ∀ ρ c, S (f ρ c) ↔ n0 ≤ ρ.val ∧ c ≠ ρ) (Y : ℕ) :
    kill S ((Matrix.of fun b c : Fin n => (MvPolynomial.X (f b c) : MvPolynomial σ R)).det ^ Y) =
      (Matrix.of fun b c : Fin n0 =>
        (MvPolynomial.X (f (Fin.castLE hn b) (Fin.castLE hn c)) : MvPolynomial σ R)).det ^ Y *
      MvPolynomial.monomial
        (∑ ρ ∈ (Finset.univ : Finset (Fin n)).filter (fun ρ => n0 ≤ ρ.val),
          Finsupp.single (f ρ ρ) Y) 1 := by sorry
