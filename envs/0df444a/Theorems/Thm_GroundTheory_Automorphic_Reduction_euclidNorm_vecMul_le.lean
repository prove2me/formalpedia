-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_euclidNorm_vecMul_le
-- name    : GroundTheory.Automorphic.Reduction.euclidNorm_vecMul_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:53:04.34987+00:00
-- url     : https://prove2.me/theorems/acc44488-b034-4318-8ed5-1d0d46a38edd
-- title:
--   Reduction: euclid Norm vec Mul le
-- statement:
--   The Reduction construction uses the euclid Norm vec Mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L100-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L100-L112

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

theorem GroundTheory.Automorphic.Reduction.euclidNorm_vecMul_le {E : Type*} [NormedField E] {M : Matrix (Fin n) (Fin n) E} {m : ℝ}
    (hm : 0 ≤ m) (hM : ∀ i j, ‖M i j‖ ≤ m) (z : Fin n → E) :
    euclidNorm (z ᵥ* M) ≤ √n * (n * m) * euclidNorm z := by sorry
