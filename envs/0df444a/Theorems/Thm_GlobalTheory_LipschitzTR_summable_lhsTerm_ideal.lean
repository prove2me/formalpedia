-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_summable_lhsTerm_ideal
-- name    : GlobalTheory.LipschitzTR.summable_lhsTerm_ideal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:56.490795+00:00
-- url     : https://prove2.me/theorems/f9940b03-1333-49e2-b5c4-4e37ae548c7d
-- title:
--   Lipschitz TR: summable lhs Term ideal
-- statement:
--   The Lipschitz TR construction uses the summable lhs Term ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableLipschitzLatticeNormPowSummand.lean#L134-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableLipschitzLatticeNormPowSummand.lean#L134-L184

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory.LipschitzTR.LhsSum

theorem GlobalTheory.LipschitzTR.summable_lhsTerm_ideal :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 →
      ∀ (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) →
        Summable (fun a : (M : Set F) => lhsTerm k z a) := by sorry
