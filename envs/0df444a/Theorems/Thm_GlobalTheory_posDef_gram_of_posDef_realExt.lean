-- Prove2me | Theorems.Thm_GlobalTheory_posDef_gram_of_posDef_realExt
-- name    : GlobalTheory.posDef_gram_of_posDef_realExt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:14:04.557568+00:00
-- url     : https://prove2.me/theorems/7e898f1b-74dd-4de2-ac4f-4543954a369b
-- title:
--   Global Theory: pos Def gram of pos Def real Ext
-- statement:
--   The Global Theory construction uses the pos Def gram of pos Def real Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L358-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L358-L377

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]

theorem GlobalTheory.posDef_gram_of_posDef_realExt {ι : Type*} [Fintype ι] (b : Basis ι ℤ X)
    {Q : QuadraticMap ℤ X ℝ} (hQ : (realExt Q).PosDef) :
    (Matrix.of fun i j => QuadraticMap.polar Q (b i) (b j)).PosDef := by sorry
