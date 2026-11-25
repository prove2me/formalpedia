-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_exists_mu_pow_eq_pow_mem
-- name    : GroundTheory.PAdicHodge.ACris.exists_mu_pow_eq_pow_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:12:22.17716+00:00
-- url     : https://prove2.me/theorems/28517e58-f426-4c1b-8189-69bdbc7d11fa
-- title:
--   ACris: exists mu pow eq pow mem
-- statement:
--   The ACris construction uses the exists mu pow eq pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L105-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L105-L149

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

theorem GroundTheory.PAdicHodge.ACris.exists_mu_pow_eq_pow_mem {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    ∃ c : ACrisZero K p,
      (algebraMap (AInf K p) (ACrisZero K p) (AInf.mu ε)) ^ (p - 1) = (p : ACrisZero K p) * c ∧
        c ^ p ∈ Ideal.span {(p : ACrisZero K p)} := by sorry
