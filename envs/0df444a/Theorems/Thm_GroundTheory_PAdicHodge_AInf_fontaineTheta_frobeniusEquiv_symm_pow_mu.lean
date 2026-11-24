-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_frobeniusEquiv_symm_pow_mu
-- name    : GroundTheory.PAdicHodge.AInf.fontaineTheta_frobeniusEquiv_symm_pow_mu
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:50.224744+00:00
-- url     : https://prove2.me/theorems/f03beb11-fbbd-4113-b81f-872dd24760b4
-- title:
--   AInf: fontaine Theta frobenius Equiv symm pow mu
-- statement:
--   The AInf construction uses the fontaine Theta frobenius Equiv symm pow mu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L87-L89

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

theorem GroundTheory.PAdicHodge.AInf.fontaineTheta_frobeniusEquiv_symm_pow_mu (ε : 𝒪♭) (n : ℕ) :
    θ (((φ).symm ^ n) (mu ε)) = PreTilt.untilt (((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) ε) - 1 := by sorry
