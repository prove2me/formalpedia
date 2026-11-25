-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_PureColPf_le_of_mul_pow_lt
-- name    : GlobalTheory.LocFlat.PureColPf.le_of_mul_pow_lt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:12.917803+00:00
-- url     : https://prove2.me/theorems/101e4d9e-a7c7-55ab-b718-78a2296ad674
-- title:
--   Pure Col Pf: le of mul pow lt
-- statement:
--   The Pure Col Pf construction uses the le of mul pow lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnIndicatorPureAtSymmetricPosition.lean#L56-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnIndicatorPureAtSymmetricPosition.lean#L56-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnIndicatorPureAtSymmetricPosition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.PureColPf
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem GlobalTheory.LocFlat.PureColPf.le_of_mul_pow_lt {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (r : ℕ) {y : k}
    (h : valuation k (y * (ϖ : k) ^ (r + 1)) < 1) : valuation k y ≤ valuation k (((ϖ ^ r)⁻¹ : kˣ) : k) := by sorry
