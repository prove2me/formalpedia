-- Prove2me | Theorems.Thm_GlobalTheory_DoublingLength_norm_pairTerm
-- name    : GlobalTheory.DoublingLength.norm_pairTerm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:52:34.735208+00:00
-- url     : https://prove2.me/theorems/240d603e-4245-4f4e-b1b2-740451a8a7da
-- title:
--   Doubling Length: norm pair Term
-- statement:
--   The Doubling Length construction uses the norm pair Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumSphericalFunctionDoublingLength.lean#L109-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumSphericalFunctionDoublingLength.lean#L109-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength
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

theorem GlobalTheory.DoublingLength.norm_pairTerm (X : ℂ) (φ : GL (Fin n) k → ℂ)
    (p : (GL (Fin n) k ⧸ KO k (Fin n)) × (GL (Fin n) k ⧸ KO k (Fin n))) :
    ((‖pairTerm X φ p‖ : ℝ) : ℂ) = pairTerm (‖X‖ : ℂ) (fun g => (‖φ g‖ : ℂ)) p := by sorry
