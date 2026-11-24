-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_constantCoeff_frobeniusEquiv_symm_pow_mu
-- name    : GroundTheory.PAdicHodge.AInf.constantCoeff_frobeniusEquiv_symm_pow_mu
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:03.380128+00:00
-- url     : https://prove2.me/theorems/2b7aab40-476d-46a4-9bda-e6c6b4db0040
-- title:
--   AInf: constant Coeff frobenius Equiv symm pow mu
-- statement:
--   The AInf construction uses the constant Coeff frobenius Equiv symm pow mu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaAInf.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaAInf.lean#L87-L91

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaAInf
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
open GroundTheory.PAdicHodge.AInf
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

theorem GroundTheory.PAdicHodge.AInf.constantCoeff_frobeniusEquiv_symm_pow_mu (ε : 𝒪♭) (N : ℕ) :
    WittVector.constantCoeff (((φ).symm ^ N) (mu ε) : AInf K p) =
      ((_root_.frobeniusEquiv 𝒪♭ p).symm ^ N) ε - 1 := by sorry
