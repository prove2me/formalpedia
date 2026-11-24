-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnipPow_pow_sub_one_apply
-- name    : GlobalTheory.RootEx.UnipPow.pow_sub_one_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:08:52.454834+00:00
-- url     : https://prove2.me/theorems/8e58e519-98a4-4b5b-90de-b2631f9166a6
-- title:
--   Unip Pow: pow sub one apply
-- statement:
--   The Unip Pow construction uses the pow sub one apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentExistsResidueCardPowMemNhds.lean#L97-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentExistsResidueCardPowMemNhds.lean#L97-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentExistsResidueCardPowMemNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnipPow
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.RootEx.UnipPow.pow_sub_one_apply {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
    {g : GL (n ⊕ Fin c) K} (hg : InN p g) (j : ℕ) :
    ∀ r s : n ⊕ Fin c, lev p s < lev p r + j →
      (((g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) K) - 1) ^ j) r s = 0 := by sorry
