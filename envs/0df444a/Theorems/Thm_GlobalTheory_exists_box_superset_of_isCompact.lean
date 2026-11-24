-- Prove2me | Theorems.Thm_GlobalTheory_exists_box_superset_of_isCompact
-- name    : GlobalTheory.exists_box_superset_of_isCompact
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:30:30.030878+00:00
-- url     : https://prove2.me/theorems/d3ef6937-353a-4831-b544-4745b959eef7
-- title:
--   Global Theory: exists box superset of is Compact
-- statement:
--   The Global Theory construction uses the exists box superset of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsIntegralScaledBoxPiSupersetOfIsCompact.lean#L17-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsIntegralScaledBoxPiSupersetOfIsCompact.lean#L17-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsIntegralScaledBoxPiSupersetOfIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
open GlobalTheory

theorem GlobalTheory.exists_box_superset_of_isCompact (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (K : Set (n → k)) :
    IsCompact K → ∀ r : kˣ, ∃ R : kˣ, valuation k (r : k) ≤ valuation k (R : k) ∧ K ⊆ box n R := by sorry
