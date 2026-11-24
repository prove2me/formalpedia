-- Prove2me | Theorems.Thm_GlobalTheory_DoublingLength_ord_det_of_mem_KO
-- name    : GlobalTheory.DoublingLength.ord_det_of_mem_KO
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:53:10.155362+00:00
-- url     : https://prove2.me/theorems/3721c0fa-f03c-4e7d-a600-e59a642aeec1
-- title:
--   Doubling Length: ord det of mem KO
-- statement:
--   The Doubling Length construction uses the ord det of mem KO property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumSphericalFunctionDoublingLength.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumSphericalFunctionDoublingLength.lean#L21-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength
import Theorems.Thm_GlobalTheory_HeckeSeries_ord_det_of_mem_KO
import Theorems.Thm_GlobalTheory_HeckeShift_ord_det_of_mem_KO
import Theorems.Thm_GlobalTheory_LatticePair_ord_det_of_mem_KO

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
open GlobalTheory GlobalTheory.DoublingLength
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem GlobalTheory.DoublingLength.ord_det_of_mem_KO {x : GL (Fin n) k} (hx : x ∈ KO k (Fin n)) :
    ord k (Matrix.GeneralLinearGroup.det x) = 0 := by sorry
