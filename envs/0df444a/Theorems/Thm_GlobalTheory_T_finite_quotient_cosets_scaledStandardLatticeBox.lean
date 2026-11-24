-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_quotient_cosets_scaledStandardLatticeBox
-- name    : GlobalTheory.T.finite_quotient_cosets_scaledStandardLatticeBox
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:20:06.629809+00:00
-- url     : https://prove2.me/theorems/bad8745f-2869-45ba-98b7-589e0f3d923b
-- title:
--   T: finite quotient cosets scaled Standard Lattice Box
-- statement:
--   The T construction uses the finite quotient cosets scaled Standard Lattice Box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteQuotientCosetsScaledStandardLatticeBoxStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteQuotientCosetsScaledStandardLatticeBoxStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteQuotientCosetsScaledStandardLatticeBox
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteQuotientCosetsScaledStandardLatticeBoxStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_quotient_cosets_scaledStandardLatticeBox : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (c₁ c₂ : kˣ), {yb : (n → k) ⧸ box n c₂ | ∃ y ∈ box n c₁, Submodule.Quotient.mk y = yb}.Finite := by sorry
