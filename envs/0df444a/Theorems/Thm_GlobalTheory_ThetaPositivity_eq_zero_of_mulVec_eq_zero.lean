-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPositivity_eq_zero_of_mulVec_eq_zero
-- name    : GlobalTheory.ThetaPositivity.eq_zero_of_mulVec_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:41:18.931999+00:00
-- url     : https://prove2.me/theorems/058f8a94-069e-55db-92fc-9be8bd285a06
-- title:
--   Theta Positivity: eq zero of mul Vec eq zero
-- statement:
--   The Theta Positivity construction uses the eq zero of mul Vec eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ReFormPosOfThetaNeZero.lean#L150-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ReFormPosOfThetaNeZero.lean#L150-L186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ReFormPosOfThetaNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaPositivity
variable {g : ℕ}

theorem GlobalTheory.ThetaPositivity.eq_zero_of_mulVec_eq_zero (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {Hm : Matrix (Fin g) (Fin g) ℂ} (Ef : LinearMap.BilinForm ℤ Λ)
    (hE : ∀ l m : Λ, (Ef l m : ℝ) =
      ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)
    (hinj : Function.Injective Ef) {w : Fin g → ℂ} (hw : Hm.mulVec (star w) = 0) : w = 0 := by sorry
