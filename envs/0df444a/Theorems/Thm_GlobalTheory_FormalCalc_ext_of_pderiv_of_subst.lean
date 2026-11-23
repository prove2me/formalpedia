-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_ext_of_pderiv_of_subst
-- name    : GlobalTheory.FormalCalc.ext_of_pderiv_of_subst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:06.690251+00:00
-- url     : https://prove2.me/theorems/b02ede9e-8f04-45fa-9ce9-5ff247ab1022
-- title:
--   Formal Calc: ext of pderiv of subst
-- statement:
--   The Formal Calc construction uses the ext of pderiv of subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L73-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Sum
variable {σ τ ι κ μ A : Type*} [CommRing A]

theorem GlobalTheory.FormalCalc.ext_of_pderiv_of_subst [IsAddTorsionFree A] (e : ι → κ) {b : κ → MvPowerSeries κ A}
    (hb0 : ∀ i, b (e i) = 0) (hb1 : ∀ k, k ∉ Set.range e → b k = X k)
    {f g : MvPowerSeries κ A} (hD : ∀ i, pderiv A (e i) f = pderiv A (e i) g)
    (h0 : subst b f = subst b g) : f = g := by sorry
