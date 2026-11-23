-- Prove2me | Theorems.Thm_GlobalTheory_DiffVanish_eval_diffTopPoly
-- name    : GlobalTheory.DiffVanish.eval_diffTopPoly
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:00:34.758905+00:00
-- url     : https://prove2.me/theorems/c33437c8-ec24-4f11-be48-8650c35502df
-- title:
--   Diff Vanish: eval diff Top Poly
-- statement:
--   The Diff Vanish construction uses the eval diff Top Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L361-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L361-L369

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G K : Type*} [AddCommGroup G] [Field K] [CharZero K]
omit [CharZero K]

theorem GlobalTheory.DiffVanish.eval_diffTopPoly {d : ℕ} {φ : G → K} (h : DiffVanish (d + 1) φ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (g : ι → G) (x : G) (n : ι → ℤ) :
    MvPolynomial.eval (fun i ↦ (n i : K)) (diffTopPoly d g φ x) =
      (d.factorial : K)⁻¹ * h.form fun _ ↦ ∑ i, n i • g i := by sorry
