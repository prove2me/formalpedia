-- Prove2me | Theorems.Thm_GlobalTheory_ConjLocal_pow_dim_mulVec
-- name    : GlobalTheory.ConjLocal.pow_dim_mulVec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:25:49.393857+00:00
-- url     : https://prove2.me/theorems/4d01e469-834b-46d5-b61f-42dd41c76c93
-- title:
--   Conj Local: pow dim mul Vec
-- statement:
--   The Conj Local construction uses the pow dim mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLinearIndependentIterates.lean#L50-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLinearIndependentIterates.lean#L50-L63

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLinearIndependentIterates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.ConjLocal
variable {R : Type} [CommRing R] {n : ℕ}

theorem GlobalTheory.ConjLocal.pow_dim_mulVec [Nontrivial R] (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (i : Fin n) :
    (Y ^ n *ᵥ v) i = -∑ k : Fin n, Y.charpoly.coeff k * (Y ^ (k : ℕ) *ᵥ v) i := by sorry
