-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_ker_fontaineTheta_comp_frobeniusEquiv_symm_eq_span
-- name    : GroundTheory.PAdicHodge.AInf.ker_fontaineTheta_comp_frobeniusEquiv_symm_eq_span
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:50.231908+00:00
-- url     : https://prove2.me/theorems/bb0c3d0b-38c4-5925-b077-67992360c975
-- title:
--   AInf: ker fontaine Theta comp frobenius Equiv symm eq span
-- statement:
--   The AInf construction uses the ker fontaine Theta comp frobenius Equiv symm eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L237-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L237-L243

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

theorem GroundTheory.PAdicHodge.AInf.ker_fontaineTheta_comp_frobeniusEquiv_symm_eq_span {ε : 𝒪♭}
    (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    RingHom.ker ((fontaineTheta (normInteger K) p).comp ((φ).symm : AInf K p ≃+* AInf K p).toRingHom) =
      Ideal.span {∑ i ∈ Finset.range p, teichmuller p ε ^ i} := by sorry
