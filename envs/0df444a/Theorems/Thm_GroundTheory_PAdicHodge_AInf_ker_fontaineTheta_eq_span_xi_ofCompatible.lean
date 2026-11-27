-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_ker_fontaineTheta_eq_span_xi_ofCompatible
-- name    : GroundTheory.PAdicHodge.AInf.ker_fontaineTheta_eq_span_xi_ofCompatible
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:01:00.976418+00:00
-- url     : https://prove2.me/theorems/91108910-576d-5087-8aec-d258f3acd5d3
-- title:
--   AInf: ker fontaine Theta eq span xi of Compatible
-- statement:
--   The AInf construction uses the ker fontaine Theta eq span xi of Compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L257-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L257-L263

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
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
open WittVector
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

theorem GroundTheory.PAdicHodge.AInf.ker_fontaineTheta_eq_span_xi_ofCompatible (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n)
    (h0 : y 0 = 1) (h1 : y 1 ≠ 1) :
    RingHom.ker θ = Ideal.span {xi (IsPerfectoidField.ofCompatible p y hy)} := by sorry
