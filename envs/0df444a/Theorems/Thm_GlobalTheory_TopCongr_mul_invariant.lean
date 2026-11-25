-- Prove2me | Theorems.Thm_GlobalTheory_TopCongr_mul_invariant
-- name    : GlobalTheory.TopCongr.mul_invariant
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:55:37.586013+00:00
-- url     : https://prove2.me/theorems/8a3deef1-27af-5b14-8402-333b2bf77320
-- title:
--   Top Congr: mul invariant
-- statement:
--   The Top Congr construction uses the mul invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CongruenceUnipotentMatrixReduction.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CongruenceUnipotentMatrixReduction.lean#L13-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CongruenceUnipotentMatrixReduction
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
open GlobalTheory GlobalTheory.TopCongr
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.TopCongr.mul_invariant {a b : Type} [Fintype a] [DecidableEq a] {f : Matrix a b k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x)
    (hp : ∀ x y, IntM x → MaxM y → f (x + y) = f x) {g : Matrix a a k} (hg : MaxM (g - 1)) (x : Matrix a b k) :
    f (g * x) = f x := by sorry
