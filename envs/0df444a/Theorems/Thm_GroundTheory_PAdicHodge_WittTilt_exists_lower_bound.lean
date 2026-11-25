-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_exists_lower_bound
-- name    : GroundTheory.PAdicHodge.WittTilt.exists_lower_bound
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:08:56.146197+00:00
-- url     : https://prove2.me/theorems/bcda4367-d0b3-428c-b991-052d47bca759
-- title:
--   Witt Tilt: exists lower bound
-- statement:
--   The Witt Tilt construction uses the exists lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonApprox.lean#L125-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonApprox.lean#L125-L200

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdRInj
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonApprox
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
open _root_.WittVector Laurent ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p
variable {ρ : ℝ}
set_option maxHeartbeats 1600000

theorem GroundTheory.PAdicHodge.WittTilt.exists_lower_bound {a : ACris K p} (ha : a ≠ 0) :
    ∃ (B : ℝ) (N₀ : ℕ), 0 < B ∧ ∀ N ≥ N₀, ∀ c : ACrisZero K p,
      a - algebraMap _ (ACris K p) c ∈ Ideal.span {(p : ACris K p) ^ N} →
        B < gn K p ‖(p : K)‖ (c : 𝔸) := by sorry
