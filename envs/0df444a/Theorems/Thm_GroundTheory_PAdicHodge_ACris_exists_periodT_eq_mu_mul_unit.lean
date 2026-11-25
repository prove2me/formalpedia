-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_exists_periodT_eq_mu_mul_unit
-- name    : GroundTheory.PAdicHodge.ACris.exists_periodT_eq_mu_mul_unit
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:11:08.763054+00:00
-- url     : https://prove2.me/theorems/d8b5e01e-0770-518b-a28a-a41933044d08
-- title:
--   ACris: exists period T eq mu mul unit
-- statement:
--   The ACris construction uses the exists period T eq mu mul unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L157-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L157-L271

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaPeriod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
set_option maxHeartbeats 1600000

theorem GroundTheory.PAdicHodge.ACris.exists_periodT_eq_mu_mul_unit {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    ∃ u : ACris K p, IsUnit u ∧
      periodT hε = algebraMap (AInf K p) (ACris K p) (AInf.mu ε) * u := by sorry
