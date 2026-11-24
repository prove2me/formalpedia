-- Prove2me | Theorems.Thm_GlobalTheory_LatticePair_valuation_det_le_one
-- name    : GlobalTheory.LatticePair.valuation_det_le_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:00:20.978696+00:00
-- url     : https://prove2.me/theorems/27f217a4-8ded-4819-8af4-84cc6d18a791
-- title:
--   Lattice Pair: valuation det le one
-- statement:
--   The Lattice Pair construction uses the valuation det le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HeckeSeriesCellHasSum.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HeckeSeriesCellHasSum.lean#L51-L56

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

theorem GlobalTheory.LatticePair.valuation_det_le_one {A : GL (Fin n) k} (hA : IsInt A) :
    valuation k ((Matrix.GeneralLinearGroup.det A : kˣ) : k) ≤ 1 := by sorry
