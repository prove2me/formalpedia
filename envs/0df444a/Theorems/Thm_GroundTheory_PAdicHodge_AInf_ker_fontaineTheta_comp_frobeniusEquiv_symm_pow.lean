-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_ker_fontaineTheta_comp_frobeniusEquiv_symm_pow
-- name    : GroundTheory.PAdicHodge.AInf.ker_fontaineTheta_comp_frobeniusEquiv_symm_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:45:49.100011+00:00
-- url     : https://prove2.me/theorems/b23634fc-ad17-4a1b-a1ff-00906208f986
-- title:
--   AInf: ker fontaine Theta comp frobenius Equiv symm pow
-- statement:
--   The AInf construction uses the ker fontaine Theta comp frobenius Equiv symm pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L255-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L255-L270

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

theorem GroundTheory.PAdicHodge.AInf.ker_fontaineTheta_comp_frobeniusEquiv_symm_pow {ξ : AInf K p}
    (hξ : RingHom.ker θ = Ideal.span {ξ}) (n : ℕ) :
    RingHom.ker ((fontaineTheta (normInteger K) p).comp ((φ).symm ^ n : AInf K p ≃+* AInf K p).toRingHom) =
      Ideal.span {(φ ^ n) ξ} := by sorry
