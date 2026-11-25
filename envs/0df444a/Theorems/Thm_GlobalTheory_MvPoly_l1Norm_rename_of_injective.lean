-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_l1Norm_rename_of_injective
-- name    : GlobalTheory.MvPoly.l1Norm_rename_of_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:18.598809+00:00
-- url     : https://prove2.me/theorems/3181725d-2be1-5742-b9dd-6554d37938fb
-- title:
--   Mv Poly: l1 Norm rename of injective
-- statement:
--   The Mv Poly construction uses the l1 Norm rename of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L134-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L134-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open GlobalTheory GlobalTheory.MvPoly
variable {σ τ K L : Type*}
variable [NormedCommRing K] [NormedCommRing L]

theorem GlobalTheory.MvPoly.l1Norm_rename_of_injective {f : σ → τ} (hf : Function.Injective f)
    (P : MvPolynomial σ K) : l1Norm (rename f P) = l1Norm P := by sorry
