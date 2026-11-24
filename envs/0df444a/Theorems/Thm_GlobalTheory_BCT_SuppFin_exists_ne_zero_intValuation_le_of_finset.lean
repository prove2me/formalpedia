-- Prove2me | Theorems.Thm_GlobalTheory_BCT_SuppFin_exists_ne_zero_intValuation_le_of_finset
-- name    : GlobalTheory.BCT.SuppFin.exists_ne_zero_intValuation_le_of_finset
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:57:53.697097+00:00
-- url     : https://prove2.me/theorems/e0413050-9fe3-484d-81ac-a59d258615ae
-- title:
--   Supp Fin: exists ne zero int Valuation le of finset
-- statement:
--   The Supp Fin construction uses the exists ne zero int Valuation le of finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfValuationBoundedNormLeOne.lean#L6-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfValuationBoundedNormLeOne.lean#L6-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfValuationBoundedNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.SuppFin

theorem GlobalTheory.BCT.SuppFin.exists_ne_zero_intValuation_le_of_finset {E : Type} [Field E] [NumberField E]
    (T : Finset (HeightOneSpectrum (𝓞 E))) (n : HeightOneSpectrum (𝓞 E) → ℕ) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ v ∈ T, v.intValuation d ≤ WithZero.exp (-(n v : ℤ)) := by sorry
