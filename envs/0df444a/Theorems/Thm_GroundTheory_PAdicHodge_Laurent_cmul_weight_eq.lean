-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_weight_eq
-- name    : GroundTheory.PAdicHodge.Laurent.cmul_weight_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:42.996485+00:00
-- url     : https://prove2.me/theorems/f11ef23e-c65a-4af3-b644-7e661da7b801
-- title:
--   Laurent: cmul weight eq
-- statement:
--   The Laurent construction uses the cmul weight eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L347-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L347-L362

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}
variable [CompleteSpace K]

theorem GroundTheory.PAdicHodge.Laurent.cmul_weight_eq (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) {n i₀ : ℤ}
    {M : ℝ} (hM : 0 < M) (heq : (‖a i₀‖ * ρ ^ i₀) * (‖b (n - i₀)‖ * ρ ^ (n - i₀)) = M)
    (hlt : ∀ i, i ≠ i₀ → (‖a i‖ * ρ ^ i) * (‖b (n - i)‖ * ρ ^ (n - i)) < M) :
    ‖cmul a b n‖ * ρ ^ n = M := by sorry
