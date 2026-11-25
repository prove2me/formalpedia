-- Prove2me | Theorems.Thm_GlobalTheory_BigOn_canonical_error_real
-- name    : GlobalTheory.BigOn.canonical_error_real
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:33:41.123808+00:00
-- url     : https://prove2.me/theorems/9c57159d-7dcc-567f-8d54-c73c5e959487
-- title:
--   Big On: canonical error real
-- statement:
--   The Big On construction uses the canonical error real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OnOfOnWithCanonical.lean#L8-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OnOfOnWithCanonical.lean#L8-L61

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OnOfOnWithCanonical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Indef Formalism.L2.Indef.Tree
open GlobalTheory GlobalTheory.BigOn

theorem GlobalTheory.BigOn.canonical_error_real {ι J : Type} [Fintype J] (T : Finset ι) (I F err err0 J0 : ι → J → ℝ)
    (e c l : ι → ℝ) (D E E' : ℝ) (hD : 0 < D) (he : ∀ w, 0 < e w) (hl : ∀ w, 0 ≤ l w) (hE : 2 * E ≤ E')
    (hJ : ∀ w ∈ T, ∀ j, 0 ≤ J0 w j)
    (h0 : ∀ w j, err0 w j =
      max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) / (e w * (Fintype.card J : ℝ)))
    (h1 : ∀ w ∈ T, ∑ j, I w j ≤ (∑ j, (2 * (e w * F w j) + e w * err w j) + c w) * D)
    (h2 : ∀ w ∈ T, ∀ j, 0 ≤ err w j)
    (h3 : ∀ j, ∑ w ∈ T, l w * (e w * err w j + e w * J0 w j) ≤ E) :
    (∀ w ∈ T, ∑ j, I w j ≤ (∑ j, (2 * (e w * F w j) + e w * err0 w j) + c w) * D) ∧
    (∀ w ∈ T, ∀ j, 0 ≤ err0 w j) ∧
    ∀ j, ∑ w ∈ T, l w * (e w * err0 w j + e w * J0 w j) ≤ E' := by sorry
