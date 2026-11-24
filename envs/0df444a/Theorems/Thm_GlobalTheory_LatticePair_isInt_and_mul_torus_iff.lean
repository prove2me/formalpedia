-- Prove2me | Theorems.Thm_GlobalTheory_LatticePair_isInt_and_mul_torus_iff
-- name    : GlobalTheory.LatticePair.isInt_and_mul_torus_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:59:53.51304+00:00
-- url     : https://prove2.me/theorems/2e47ddf9-c90d-4055-bc40-0b00edfb6641
-- title:
--   Lattice Pair: is Int and mul torus iff
-- statement:
--   The Lattice Pair construction uses the is Int and mul torus iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HeckeSeriesCellHasSum.lean#L81-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HeckeSeriesCellHasSum.lean#L81-L108

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

theorem GlobalTheory.LatticePair.isInt_and_mul_torus_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (A : GL (Fin n) k)
    (e : Fin n → ℤ) : IsInt A ∧ IsInt (A * torusElt k (Fin n) ϖ e) ↔
      IsInt (A * torusElt k (Fin n) ϖ fun i => min (e i) 0) := by sorry
