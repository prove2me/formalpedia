-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_thetaZero_dpow
-- name    : GroundTheory.PAdicHodge.ACris.thetaZero_dpow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:50.059106+00:00
-- url     : https://prove2.me/theorems/20b6e69c-fd76-5116-bcc5-d30159e59e6e
-- title:
--   ACris: theta Zero dpow
-- statement:
--   The ACris construction uses the theta Zero dpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FactorizationFactorialLe.lean#L237-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FactorizationFactorialLe.lean#L237-L239

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
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
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)

theorem GroundTheory.PAdicHodge.ACris.thetaZero_dpow {x : AInf K p} (hx : x ∈ RingHom.ker θ) {n : ℕ} (hn : n ≠ 0) :
    thetaZero K p ⟨dpow n x, dpow_mem hx n⟩ = 0 := by sorry
