-- Prove2me | Theorems.Thm_GlobalTheory_BddFinite_exists_clearing
-- name    : GlobalTheory.BddFinite.exists_clearing
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:59:53.85698+00:00
-- url     : https://prove2.me/theorems/cc9f9953-a491-44d3-88d2-25bc18d97493
-- title:
--   Bdd Finite: exists clearing
-- statement:
--   The Bdd Finite construction uses the exists clearing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfBoundedEmbeddingsAndValuations.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfBoundedEmbeddingsAndValuations.lean#L15-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfBoundedEmbeddingsAndValuations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
open GlobalTheory GlobalTheory.BddFinite

theorem GlobalTheory.BddFinite.exists_clearing {K : Type} [Field K] [NumberField K] (A : Set K)
    (w : HeightOneSpectrum (𝓞 K)) (B : WithZero (Multiplicative ℤ))
    (hB : ∀ x ∈ A, w.valuation K x ≤ B) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ x ∈ A, w.valuation K ((a : K) * x) ≤ 1 := by sorry
