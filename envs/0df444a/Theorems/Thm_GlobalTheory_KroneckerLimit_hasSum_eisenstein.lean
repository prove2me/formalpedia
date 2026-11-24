-- Prove2me | Theorems.Thm_GlobalTheory_KroneckerLimit_hasSum_eisenstein
-- name    : GlobalTheory.KroneckerLimit.hasSum_eisenstein
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:27.855812+00:00
-- url     : https://prove2.me/theorems/a9ae510d-d61a-46ec-8029-cd6dec00d96a
-- title:
--   Kronecker Limit: has Sum eisenstein
-- statement:
--   The Kronecker Limit construction uses the has Sum eisenstein property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoRealEisensteinSubPole.lean#L321-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoRealEisensteinSubPole.lean#L321-L340

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory GlobalTheory.KroneckerLimit

theorem GlobalTheory.KroneckerLimit.hasSum_eisenstein (τ : UpperHalfPlane) {s : ℝ} (hs : 1 < s) :
    HasSum (fun p : {p : ℤ × ℤ // p ≠ 0} =>
        τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s))
      (τ.im ^ s * (rowSum 0 0 s + 2 * (∑' m, rowError τ.re τ.im m s))
        + 2 * (betaConst s * τ.im ^ (1 - s)) * ∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) := by sorry
