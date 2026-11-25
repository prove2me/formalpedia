-- Prove2me | Theorems.Thm_GlobalTheory_DiagBlock_coeff_kill
-- name    : GlobalTheory.DiagBlock.coeff_kill
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:44:24.095799+00:00
-- url     : https://prove2.me/theorems/b5cb5986-2a50-49e1-a45f-8f9a49e5f5e0
-- title:
--   Diag Block: coeff kill
-- statement:
--   The Diag Block construction uses the coeff kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L68-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L68-L78

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
variable {R : Type} [CommRing R] {σ : Type}
open Classical

theorem GlobalTheory.DiagBlock.coeff_kill (S : σ → Prop) [DecidablePred S] (P : MvPolynomial σ R) (e : σ →₀ ℕ) :
    MvPolynomial.coeff e (kill S P) =
      if ∀ x, S x → e x = 0 then MvPolynomial.coeff e P else 0 := by sorry
