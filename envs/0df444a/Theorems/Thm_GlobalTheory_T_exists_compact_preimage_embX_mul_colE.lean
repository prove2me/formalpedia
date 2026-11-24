-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_compact_preimage_embX_mul_colE
-- name    : GlobalTheory.T.exists_compact_preimage_embX_mul_colE
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:34:02.039667+00:00
-- url     : https://prove2.me/theorems/86bcd1d0-6839-4e82-b37c-89a7418f97b9
-- title:
--   T: exists compact preimage emb X mul col E
-- statement:
--   The T construction uses the exists compact preimage emb X mul col E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ProperTripleStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ProperTripleStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ProperTriple
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ProperTripleStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_compact_preimage_embX_mul_colE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (C : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact C), ∃ D : Set (GL n k × N k n c (ρ + 1) × (n → k)), IsCompact D ∧ ∀ z : GL n k × N k n c (ρ + 1) × (n → k), embX c z.1 * (z.2.1 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) z.2.2 ∈ C → z ∈ D := by sorry
