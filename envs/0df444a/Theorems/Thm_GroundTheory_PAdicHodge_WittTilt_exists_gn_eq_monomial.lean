-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_exists_gn_eq_monomial
-- name    : GroundTheory.PAdicHodge.WittTilt.exists_gn_eq_monomial
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:13:40.504407+00:00
-- url     : https://prove2.me/theorems/79f4749b-ffd2-5f86-a1fc-8612e190c364
-- title:
--   Witt Tilt: exists gn eq monomial
-- statement:
--   The Witt Tilt construction uses the exists gn eq monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonSlope.lean#L23-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonSlope.lean#L23-L92

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonApprox
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonSlope
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
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector Laurent Filter Topology
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝔸" => Localization.Away (p : AInf K p)

theorem GroundTheory.PAdicHodge.WittTilt.exists_gn_eq_monomial {z : 𝔸} (hz : z ≠ 0) {r₀ : ℝ} (hr0 : 0 < r₀) (hr1 : r₀ < 1) :
    ∃ (β : ℝ) (i : ℤ) (ρ₃ : ℝ), 0 < β ∧ r₀ < ρ₃ ∧ ρ₃ < 1 ∧
      ∀ ρ ∈ Set.Icc r₀ ρ₃, gn K p ρ z = β * ρ ^ i := by sorry
