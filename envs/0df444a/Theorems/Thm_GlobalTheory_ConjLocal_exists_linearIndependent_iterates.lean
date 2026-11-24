-- Prove2me | Theorems.Thm_GlobalTheory_ConjLocal_exists_linearIndependent_iterates
-- name    : GlobalTheory.ConjLocal.exists_linearIndependent_iterates
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:26:01.399328+00:00
-- url     : https://prove2.me/theorems/6f50bb5f-6938-403a-8abb-7a5cafee9b4d
-- title:
--   Conj Local: exists linear Independent iterates
-- statement:
--   The Conj Local construction uses the exists linear Independent iterates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLinearIndependentIterates.lean#L15-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLinearIndependentIterates.lean#L15-L42

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

theorem GlobalTheory.ConjLocal.exists_linearIndependent_iterates {K : Type} [Field K] (M : Matrix (Fin n) (Fin n) K)
    (hs : M.charpoly.Separable) :
    ∃ v : Fin n → K, LinearIndependent K (fun j : Fin n => (M ^ (j : ℕ)) *ᵥ v) := by sorry
