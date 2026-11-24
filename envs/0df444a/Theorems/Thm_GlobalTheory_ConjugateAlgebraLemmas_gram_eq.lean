-- Prove2me | Theorems.Thm_GlobalTheory_ConjugateAlgebraLemmas_gram_eq
-- name    : GlobalTheory.ConjugateAlgebraLemmas.gram_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:25:24.389809+00:00
-- url     : https://prove2.me/theorems/69597671-5732-46b5-ab76-40b441c02fb2
-- title:
--   Conjugate Algebra Lemmas: gram eq
-- statement:
--   The Conjugate Algebra Lemmas construction uses the gram eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjAlgApply.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjAlgApply.lean#L35-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjAlgApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConjugateAlgebraLemmas
open Matrix

theorem GlobalTheory.ConjugateAlgebraLemmas.gram_eq {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : (g.map σ)ᵀ * g = 1) (a b : Fin n → K) :
    ∑ k : Fin n, σ ((g *ᵥ a) k) * (g *ᵥ b) k = ∑ k : Fin n, σ (a k) * b k := by sorry
