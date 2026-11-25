-- Prove2me | Theorems.Thm_GlobalTheory_Nef_nrm_coeff_prod_linear
-- name    : GlobalTheory.Nef.nrm_coeff_prod_linear
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:01:59.106998+00:00
-- url     : https://prove2.me/theorems/d3957fd0-8dd0-4a82-b118-801dc4d32dbb
-- title:
--   Nef: nrm coeff prod linear
-- statement:
--   The Nef construction uses the nrm coeff prod linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NrmCoeffProdLinear.lean#L76-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NrmCoeffProdLinear.lean#L76-L91

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

theorem GlobalTheory.Nef.nrm_coeff_prod_linear : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ (v : Place k F) (m : ℕ) (α β : Fin m → F), nrm v (fun a : Fin (m + 1) => (∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).coeff a) = ∏ j, max (v.1 (α j)) (v.1 (β j)) := by sorry
