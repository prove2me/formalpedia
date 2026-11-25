-- Prove2me | Theorems.Thm_GlobalTheory_DomainDens_blockSym_apply
-- name    : GlobalTheory.DomainDens.blockSym_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:08.10559+00:00
-- url     : https://prove2.me/theorems/0c973876-e2f3-4c6e-ade5-bb30c3030ff4
-- title:
--   Domain Dens: block Sym apply
-- statement:
--   The Domain Dens construction uses the block Sym apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/BlockSymApply.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/BlockSymApply.lean#L16-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_BlockSymApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.DomainDens

theorem GlobalTheory.DomainDens.blockSym_apply {ι : Type} {p q n : ℕ} [Fintype ι] (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι)
    (i j : Fin p) : blockSym h τ i j =
      ∑ b : Fin q, X (Fintype.equivFinOfCardEq h (τ, i, b), Fintype.equivFinOfCardEq h (τ, j, b)) := by sorry
