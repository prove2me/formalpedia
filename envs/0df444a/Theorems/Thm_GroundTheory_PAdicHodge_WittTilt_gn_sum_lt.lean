-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_sum_lt
-- name    : GroundTheory.PAdicHodge.WittTilt.gn_sum_lt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:18:29.475605+00:00
-- url     : https://prove2.me/theorems/dcd4643a-9c78-43a2-a2e4-a4625a46b5c9
-- title:
--   Witt Tilt: gn sum lt
-- statement:
--   The Witt Tilt construction uses the gn sum lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonDom.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonDom.lean#L20-L28

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

theorem GroundTheory.PAdicHodge.WittTilt.gn_sum_lt (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ι : Type*} (s : Finset ι) (f : ι → 𝔸) {M : ℝ}
    (hM : 0 < M) (h : ∀ i ∈ s, gn K p ρ (f i) < M) : gn K p ρ (∑ i ∈ s, f i) < M := by sorry
