-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_frobeniusEquiv_symm_mu_ne_zero
-- name    : GroundTheory.PAdicHodge.AInf.frobeniusEquiv_symm_mu_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:49.201993+00:00
-- url     : https://prove2.me/theorems/ec8bc26f-5f4e-4de5-86a0-cf8a53313e1b
-- title:
--   AInf: frobenius Equiv symm mu ne zero
-- statement:
--   The AInf construction uses the frobenius Equiv symm mu ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L106-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L106-L112

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

theorem GroundTheory.PAdicHodge.AInf.frobeniusEquiv_symm_mu_ne_zero {ε : 𝒪♭} (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    (φ).symm (mu ε) ≠ 0 := by sorry
