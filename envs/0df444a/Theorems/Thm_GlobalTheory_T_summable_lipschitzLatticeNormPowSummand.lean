-- Prove2me | Theorems.Thm_GlobalTheory_T_summable_lipschitzLatticeNormPowSummand
-- name    : GlobalTheory.T.summable_lipschitzLatticeNormPowSummand
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:59:28.280806+00:00
-- url     : https://prove2.me/theorems/6a13ae94-7b69-42ae-b21e-cc935603d1c4
-- title:
--   T: summable lipschitz Lattice Norm Pow Summand
-- statement:
--   The T construction uses the summable lipschitz Lattice Norm Pow Summand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableLipschitzLatticeNormPowSummandStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableLipschitzLatticeNormPowSummandStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummandStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.summable_lipschitzLatticeNormPowSummand : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 → ∀ (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) → Summable (fun a : (M : Set F) => lhsTerm k z a) := by sorry
