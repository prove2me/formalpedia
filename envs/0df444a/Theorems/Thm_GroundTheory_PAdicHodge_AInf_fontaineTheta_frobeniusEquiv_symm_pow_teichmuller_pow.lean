-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_frobeniusEquiv_symm_pow_teichmuller_pow
-- name    : GroundTheory.PAdicHodge.AInf.fontaineTheta_frobeniusEquiv_symm_pow_teichmuller_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:51.698549+00:00
-- url     : https://prove2.me/theorems/b7a3b9f6-30b5-4f16-a460-e42c4545ffa5
-- title:
--   AInf: fontaine Theta frobenius Equiv symm pow teichmuller pow
-- statement:
--   The AInf construction uses the fontaine Theta frobenius Equiv symm pow teichmuller pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L250-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L250-L253

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
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
open WittVector
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

theorem GroundTheory.PAdicHodge.AInf.fontaineTheta_frobeniusEquiv_symm_pow_teichmuller_pow (x : 𝒪♭) (n : ℕ) :
    θ (((φ).symm ^ n) (teichmuller p x)) ^ p ^ n = PreTilt.untilt x := by sorry
