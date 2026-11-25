-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_sub_le_of_mem
-- name    : GroundTheory.PAdicHodge.WittTilt.gn_sub_le_of_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:08.451649+00:00
-- url     : https://prove2.me/theorems/6a160ed4-2082-4147-8a00-39e74e3390d9
-- title:
--   Witt Tilt: gn sub le of mem
-- statement:
--   The Witt Tilt construction uses the gn sub le of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonApprox.lean#L53-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonApprox.lean#L53-L62

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

theorem GroundTheory.PAdicHodge.WittTilt.gn_sub_le_of_mem (hp0 : ‖(p : K)‖ ≤ ρ) (hρ1 : ρ < 1) {c₁ c₂ : ACrisZero K p} {N : ℕ}
    (h : algebraMap _ (ACris K p) c₁ - algebraMap _ (ACris K p) c₂ ∈
      Ideal.span {(p : ACris K p) ^ N}) :
    gn K p ρ ((c₁ : 𝔸) - c₂) ≤ ρ ^ N := by sorry
