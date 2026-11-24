-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ParabolicEntries_embX_mem_R
-- name    : GlobalTheory.RootEx.ParabolicEntries.embX_mem_R
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:26:06.249819+00:00
-- url     : https://prove2.me/theorems/86582f0b-2d9b-4e3f-9e22-5739135a9027
-- title:
--   Parabolic Entries: emb X mem R
-- statement:
--   The Parabolic Entries construction uses the emb X mem R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemRootExchangeParabolicAndFourierJacobiIffEntri.lean#L110-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemRootExchangeParabolicAndFourierJacobiIffEntri.lean#L110-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemRootExchangeParabolicAndFourierJacobiIffEntri
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ParabolicEntries
open GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.RootEx.ParabolicEntries.embX_mem_R (p : ℕ) (x : GL n k) : embX c x ∈ R k n c p := by sorry
