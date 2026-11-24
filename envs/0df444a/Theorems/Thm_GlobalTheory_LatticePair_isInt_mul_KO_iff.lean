-- Prove2me | Theorems.Thm_GlobalTheory_LatticePair_isInt_mul_KO_iff
-- name    : GlobalTheory.LatticePair.isInt_mul_KO_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:00:04.07562+00:00
-- url     : https://prove2.me/theorems/42ddb05f-8d7b-46d0-b899-d91e9b9bd606
-- title:
--   Lattice Pair: is Int mul KO iff
-- statement:
--   The Lattice Pair construction uses the is Int mul KO iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HeckeSeriesCellHasSum.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HeckeSeriesCellHasSum.lean#L19-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.LatticePair
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem GlobalTheory.LatticePair.isInt_mul_KO_iff {A κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) : IsInt (A * κ) ↔ IsInt A := by sorry
