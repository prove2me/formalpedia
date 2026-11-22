-- Prove2me | Theorems.Thm_GlobalTheory_NatCastUnitNorm_norm_natCast_eq_one_of_not_dvd
-- name    : GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:58.737483+00:00
-- url     : https://prove2.me/theorems/3c783eb6-153b-4058-a70c-16d162627ca3
-- title:
--   Nat Cast Unit Norm: norm nat Cast eq one of not dvd
-- statement:
--   The Nat Cast Unit Norm construction uses the norm nat Cast eq one of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormNatCastEqOneOfNotDvd.lean#L7-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormNatCastEqOneOfNotDvd.lean#L7-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormNatCastEqOneOfNotDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.NatCastUnitNorm

theorem GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K]
    {l m : ℕ} (hl : Nat.Prime l) (hlt : ‖(l : K)‖ < (1 : ℝ)) (hm : ¬ l ∣ m) :
    ‖(m : K)‖ = (1 : ℝ) := by sorry
