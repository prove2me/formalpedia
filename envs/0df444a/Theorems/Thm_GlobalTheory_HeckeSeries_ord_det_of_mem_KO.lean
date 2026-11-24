-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSeries_ord_det_of_mem_KO
-- name    : GlobalTheory.HeckeSeries.ord_det_of_mem_KO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:33.46116+00:00
-- url     : https://prove2.me/theorems/c4f8ed39-6826-4726-a374-abaf6b947652
-- title:
--   Hecke Series: ord det of mem KO
-- statement:
--   The Hecke Series construction uses the ord det of mem KO property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumHeckeSeriesBorelSphericalIntegralCosets.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumHeckeSeriesBorelSphericalIntegralCosets.lean#L16-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesBorelSphericalIntegralCosets
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
open GlobalTheory GlobalTheory.HeckeSeries
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {p : 𝒪[k]}

theorem GlobalTheory.HeckeSeries.ord_det_of_mem_KO {y : GL (Fin n) k} (hy : y ∈ KO k (Fin n)) :
    ord k (Matrix.GeneralLinearGroup.det y) = 0 := by sorry
