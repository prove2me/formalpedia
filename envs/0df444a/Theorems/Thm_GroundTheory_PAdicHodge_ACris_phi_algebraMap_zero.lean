-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_phi_algebraMap_zero
-- name    : GroundTheory.PAdicHodge.ACris.phi_algebraMap_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:16:07.833993+00:00
-- url     : https://prove2.me/theorems/69a186ba-0546-42b6-a7e3-7c05bee80909
-- title:
--   ACris: phi algebra Map zero
-- statement:
--   The ACris construction uses the phi algebra Map zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L239-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L239-L242

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
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
open _root_.WittVector Polynomial
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
local notation "𝔭₀" => Ideal.span {(p : ACrisZero K p)}
variable {x : AInf K p}

theorem GroundTheory.PAdicHodge.ACris.phi_algebraMap_zero (y : ACrisZero K p) :
    phi K p (algebraMap (ACrisZero K p) (ACris K p) y) =
      algebraMap (ACrisZero K p) (ACris K p) (phiZero K p y) := by sorry
