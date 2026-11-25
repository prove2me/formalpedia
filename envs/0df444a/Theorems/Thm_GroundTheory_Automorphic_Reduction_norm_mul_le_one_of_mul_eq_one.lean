-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_mul_le_one_of_mul_eq_one
-- name    : GroundTheory.Automorphic.Reduction.norm_mul_le_one_of_mul_eq_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:05:13.830234+00:00
-- url     : https://prove2.me/theorems/b6d40241-2a80-464c-9f8c-d5059571ddb2
-- title:
--   Reduction: norm mul le one of mul eq one
-- statement:
--   The Reduction construction uses the norm mul le one of mul eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L295-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L295-L300

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.norm_mul_le_one_of_mul_eq_one {E : Type*} [NormedField E] {a a' b : E} (h : a * a' = 1)
    (hb : ‖b‖ ≤ ‖a‖) : ‖a' * b‖ ≤ 1 := by sorry
