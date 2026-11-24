-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_frobeniusEquiv_symm_ofCompatible
-- name    : GroundTheory.PAdicHodge.AInf.frobeniusEquiv_symm_ofCompatible
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:44:08.937498+00:00
-- url     : https://prove2.me/theorems/2e37a387-3187-4ee9-9d56-a462fef5fa94
-- title:
--   AInf: frobenius Equiv symm of Compatible
-- statement:
--   The AInf construction uses the frobenius Equiv symm of Compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L250-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L250-L255

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

theorem GroundTheory.PAdicHodge.AInf.frobeniusEquiv_symm_ofCompatible (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n) :
    (_root_.frobeniusEquiv 𝒪♭ p).symm (IsPerfectoidField.ofCompatible p y hy) =
      IsPerfectoidField.ofCompatible p (fun n => y (n + 1)) (fun n => hy (n + 1)) := by sorry
