-- Prove2me | Theorems.Thm_GlobalTheory_exists_notMem_mul_valuation_le_one_of_ne
-- name    : GlobalTheory.exists_notMem_mul_valuation_le_one_of_ne
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:23.945434+00:00
-- url     : https://prove2.me/theorems/d4f66fe7-2a9b-49d7-bd30-8909fbd3494b
-- title:
--   Global Theory: exists not Mem mul valuation le one of ne
-- statement:
--   The Global Theory construction uses the exists not Mem mul valuation le one of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotMemMulValuationLeOneOfNe.lean#L6-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotMemMulValuationLeOneOfNe.lean#L6-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotMemMulValuationLeOneOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory

theorem GlobalTheory.exists_notMem_mul_valuation_le_one_of_ne : ∀ {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (𝓞 F)) {ι : Type} [Finite ι] (x : ι → F), ∃ s : 𝓞 F, s ∉ p.asIdeal ∧
      ∀ q : HeightOneSpectrum (𝓞 F), q ≠ p → ∀ i, q.valuation F ((s : F) * x i) ≤ 1 := by sorry
