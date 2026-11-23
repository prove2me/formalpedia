-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_VolN_sum_extendByZero_fin_eq_sum_of_eq
-- name    : GlobalTheory.RootEx.VolN.sum_extendByZero_fin_eq_sum_of_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:22.622808+00:00
-- url     : https://prove2.me/theorems/58d524f2-694b-493e-81a2-d1ba81c3abc2
-- title:
--   Vol N: sum extend By Zero fin eq sum of eq
-- statement:
--   The Vol N construction uses the sum extend By Zero fin eq sum of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L27-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L27-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem GlobalTheory.RootEx.VolN.sum_extendByZero_fin_eq_sum_of_eq (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}]
    (e : {rs : ι × ι // P rs.1 rs.2} → k) (w : ι × ι → k) :
    ∑ b : {rs : ι × ι // P rs.1 rs.2}, w b.1 * e b = ∑ r, ∑ s, w (r, s) * ext0 P e r s := by sorry
