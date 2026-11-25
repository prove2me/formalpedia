-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ParabolicEntries_exists_eq_embX_mul
-- name    : GlobalTheory.RootEx.ParabolicEntries.exists_eq_embX_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:25:59.240818+00:00
-- url     : https://prove2.me/theorems/5b33b3b9-303e-4e7c-b3e1-4d30d6a7d827
-- title:
--   Parabolic Entries: exists eq emb X mul
-- statement:
--   The Parabolic Entries construction uses the exists eq emb X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemRootExchangeParabolicAndFourierJacobiIffEntri.lean#L87-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemRootExchangeParabolicAndFourierJacobiIffEntri.lean#L87-L108

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

theorem GlobalTheory.RootEx.ParabolicEntries.exists_eq_embX_mul {L : ℕ} {b : Fin c → ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ parGroup k n L b) :
    ∃ (x : GL n k) (u : GL (n ⊕ Fin c) k), Uni (Sum.elim (fun _ => L) b) u.val ∧ g = embX c x * u := by sorry
