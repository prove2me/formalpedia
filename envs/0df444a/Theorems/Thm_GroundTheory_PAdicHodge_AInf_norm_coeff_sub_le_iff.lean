-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_coeff_sub_le_iff
-- name    : GroundTheory.PAdicHodge.AInf.norm_coeff_sub_le_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:17.000807+00:00
-- url     : https://prove2.me/theorems/e728c49c-535e-4aca-a7c1-249c0cf6683a
-- title:
--   AInf: norm coeff sub le iff
-- statement:
--   The AInf construction uses the norm coeff sub le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L88-L91

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
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
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p

theorem GroundTheory.PAdicHodge.AInf.norm_coeff_sub_le_iff (ϖ : 𝒪♭) (k n : ℕ) (x y : AInf K p) :
    (∀ i < n, ‖x.coeff i - y.coeff i‖ ≤ ‖ϖ‖ ^ k) ↔ ∀ i < n, ‖(x - y).coeff i‖ ≤ ‖ϖ‖ ^ k := by sorry
