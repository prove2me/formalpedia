-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_sum_sub_sum_mem
-- name    : GroundTheory.PAdicHodge.WittTilt.sum_sub_sum_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:02.601507+00:00
-- url     : https://prove2.me/theorems/ea0e0fbc-d6ad-527c-af12-8f9b8eed3fd2
-- title:
--   Witt Tilt: sum sub sum mem
-- statement:
--   The Witt Tilt construction uses the sum sub sum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonDom.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonDom.lean#L30-L35

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonApprox
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonDom
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
local notation "𝔸" => Localization.Away (p : AInf K p)
variable {ρ : ℝ}

theorem GroundTheory.PAdicHodge.WittTilt.sum_sub_sum_mem {R : Type*} [CommRing R] (I : Ideal R) (d : ℕ) (C : ℕ → R) {a a' b b' : R}
    (ha : a - a' ∈ I) (hb : b - b' ∈ I) :
    ∑ i ∈ Finset.range (d + 1), C i * a ^ i * b ^ (d - i) -
      ∑ i ∈ Finset.range (d + 1), C i * a' ^ i * b' ^ (d - i) ∈ I := by sorry
