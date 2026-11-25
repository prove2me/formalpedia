-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_vecMul_le_of_norm_le
-- name    : GroundTheory.Automorphic.Reduction.norm_vecMul_le_of_norm_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:03:51.757486+00:00
-- url     : https://prove2.me/theorems/d55258c5-dd8d-5a22-a476-7b28d57419cd
-- title:
--   Reduction: norm vec Mul le of norm le
-- statement:
--   The Reduction construction uses the norm vec Mul le of norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L90-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L90-L98

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

theorem GroundTheory.Automorphic.Reduction.norm_vecMul_le_of_norm_le (v : HeightOneSpectrum (𝓞 K))
    {M : Matrix (Fin n) (Fin n) (v.adicCompletion K)} {m : ℝ} (hm : 0 ≤ m)
    (hM : ∀ i j, ‖M i j‖ ≤ m) (z : Fin n → v.adicCompletion K) : ‖z ᵥ* M‖ ≤ m * ‖z‖ := by sorry
