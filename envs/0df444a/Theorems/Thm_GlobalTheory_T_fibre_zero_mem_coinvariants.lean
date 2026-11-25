-- Prove2me | Theorems.Thm_GlobalTheory_T_fibre_zero_mem_coinvariants
-- name    : GlobalTheory.T.fibre_zero_mem_coinvariants
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:32:43.666419+00:00
-- url     : https://prove2.me/theorems/bafffe24-df2e-4910-9038-cb0e76e3a417
-- title:
--   T: fibre zero mem coinvariants
-- statement:
--   The T construction uses the fibre zero mem coinvariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FibreZeroMemCoinvariantsStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FibreZeroMemCoinvariantsStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreZeroMemCoinvariants
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreZeroMemCoinvariantsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fibre_zero_mem_coinvariants : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), GlobalTheory.RankFibre.fibre ν β a b Φ = 0 → Φ ∈ GlobalTheory.RankFibre.coinv ν β a (a + b) := by sorry
