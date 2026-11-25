-- Prove2me | Theorems.Thm_GlobalTheory_Nef_coeff_max_prod_linear
-- name    : GlobalTheory.Nef.coeff_max_prod_linear
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:36.802474+00:00
-- url     : https://prove2.me/theorems/62051a63-f873-45c1-9e17-733be46afba8
-- title:
--   Nef: coeff max prod linear
-- statement:
--   The Nef construction uses the coeff max prod linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NrmCoeffProdLinear.lean#L63-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NrmCoeffProdLinear.lean#L63-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NrmCoeffProdLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
open Polynomial

theorem GlobalTheory.Nef.coeff_max_prod_linear {F Γ ι : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    (α β : ι → F) (s : Finset ι) :
    (∀ i, v ((∏ j ∈ s, (C (α j) + C (β j) * X)).coeff i) ≤ ∏ j ∈ s, max (v (α j)) (v (β j))) ∧
      ∃ i, v ((∏ j ∈ s, (C (α j) + C (β j) * X)).coeff i) = ∏ j ∈ s, max (v (α j)) (v (β j)) := by sorry
