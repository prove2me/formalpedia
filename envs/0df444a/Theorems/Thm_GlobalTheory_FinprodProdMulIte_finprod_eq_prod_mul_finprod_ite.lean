-- Prove2me | Theorems.Thm_GlobalTheory_FinprodProdMulIte_finprod_eq_prod_mul_finprod_ite
-- name    : GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:32:52.147872+00:00
-- url     : https://prove2.me/theorems/adc323ac-7aa0-5ecb-9615-8d6c1a9f48c8
-- title:
--   Finprod Prod Mul Ite: finprod eq prod mul finprod ite
-- statement:
--   The Finprod Prod Mul Ite construction uses the finprod eq prod mul finprod ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FinprodEqProdMulFinprodIte.lean#L7-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FinprodEqProdMulFinprodIte.lean#L7-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FinprodEqProdMulFinprodIte
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinprodProdMulIte
open Classical

theorem GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite {ι : Type} (S₁ : Finset ι) (f g : ι → ℂ)
    (hf : (Function.mulSupport f).Finite) (hfg : ∀ p, p ∉ S₁ → f p = g p) :
    ∏ᶠ p, f p = (∏ p ∈ S₁, f p) * ∏ᶠ p, (if p ∈ S₁ then (1 : ℂ) else g p) := by sorry
