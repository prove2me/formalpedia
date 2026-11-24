-- Prove2me | Theorems.Thm_GlobalTheory_T_hasFDerivAt_deformedProductDerivativeTerm
-- name    : GlobalTheory.T.hasFDerivAt_deformedProductDerivativeTerm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:42:33.524411+00:00
-- url     : https://prove2.me/theorems/60f28fa7-0f89-4aac-ac61-abc901eda17c
-- title:
--   T: has FDeriv At deformed Product Derivative Term
-- statement:
--   The T construction uses the has FDeriv At deformed Product Derivative Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasFDerivAtDeformedProductDerivativeTermStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasFDerivAtDeformedProductDerivativeTermStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFDerivAtDeformedProductDerivativeTerm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFDerivAtDeformedProductDerivativeTermStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasFDerivAt_deformedProductDerivativeTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I, HasFDerivAt (fun w : I → ℂ => dTerm φ k m w x) (∑ j, dTerm φ k (m + Pi.single j 1) z x • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j)) z := by sorry
