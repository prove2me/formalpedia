-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_acrisZero_eq_adjoin
-- name    : GroundTheory.PAdicHodge.ACris.acrisZero_eq_adjoin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:02:59.935569+00:00
-- url     : https://prove2.me/theorems/56ef4ee3-c64d-4ec7-b3aa-9b042aa3fbbf
-- title:
--   ACris: acris Zero eq adjoin
-- statement:
--   The ACris construction uses the acris Zero eq adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FactorizationFactorialLe.lean#L159-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FactorizationFactorialLe.lean#L159-L171

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
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
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)

theorem GroundTheory.PAdicHodge.ACris.acrisZero_eq_adjoin {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ}) :
    ACrisZero K p = Algebra.adjoin (AInf K p) (Set.range fun n : ℕ => dpow n ξ) := by sorry
