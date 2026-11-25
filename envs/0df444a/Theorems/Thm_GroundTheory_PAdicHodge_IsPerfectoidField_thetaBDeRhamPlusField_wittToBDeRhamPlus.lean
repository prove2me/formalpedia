-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_thetaBDeRhamPlusField_wittToBDeRhamPlus
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:54.023168+00:00
-- url     : https://prove2.me/theorems/281bf93b-2bce-4edf-a2a5-089c046b2e1b
-- title:
--   Is Perfectoid Field: theta BDe Rham Plus Field witt To BDe Rham Plus
-- statement:
--   The Is Perfectoid Field construction uses the theta BDe Rham Plus Field witt To BDe Rham Plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L431-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L431-L434

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
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
open Ideal WittVector IsLocalRing
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔹" => BDeRhamPlus (normInteger K) p

theorem GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus [CharZero K] (x : 𝕎𝒪♭) :
    thetaBDeRhamPlusField p (wittToBDeRhamPlus 𝒪 p x) = (θ x : K) := by sorry
