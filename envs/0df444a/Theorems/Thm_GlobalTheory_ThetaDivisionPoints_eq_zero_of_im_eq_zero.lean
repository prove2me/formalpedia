-- Prove2me | Theorems.Thm_GlobalTheory_ThetaDivisionPoints_eq_zero_of_im_eq_zero
-- name    : GlobalTheory.ThetaDivisionPoints.eq_zero_of_im_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:28:42.934823+00:00
-- url     : https://prove2.me/theorems/8767bb3c-82a3-5edb-8184-512236fd1c20
-- title:
--   Theta Division Points: eq zero of im eq zero
-- statement:
--   The Theta Division Points construction uses the eq zero of im eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThetaFunctionNeZeroAtDivisionPointSelfDual.lean#L9-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThetaFunctionNeZeroAtDivisionPointSelfDual.lean#L9-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsThetaDivisionPointNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ThetaFunctionNeZeroAtDivisionPointSelfDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open GlobalTheory GlobalTheory.ThetaDivisionPoints

theorem GlobalTheory.ThetaDivisionPoints.eq_zero_of_im_eq_zero {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) {S : Set (Fin g → ℂ)}
    (hS : Submodule.span ℝ S = ⊤) {z : Fin g → ℂ}
    (hz : ∀ m ∈ S, (z ⬝ᵥ Hm.mulVec (star m)).im = 0) : z = 0 := by sorry
