-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_finite_smul_mem_of_height_le
-- name    : GroundTheory.Automorphic.Reduction.exists_finite_smul_mem_of_height_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:42.696079+00:00
-- url     : https://prove2.me/theorems/ab08da7b-da97-4345-850e-cfe7fd9c2503
-- title:
--   Reduction: exists finite smul mem of height le
-- statement:
--   The Reduction construction uses the exists finite smul mem of height le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L302-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L302-L383

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

theorem GroundTheory.Automorphic.Reduction.exists_finite_smul_mem_of_height_le {C : Set (AdelicGLn.AdelicGL K n)} (hC : IsCompact C)
    (B : ℝ) : ∃ F : Set (Fin n → K), F.Finite ∧ ∀ g ∈ C, ∀ x : Fin n → K, x ≠ 0 →
      height g x ≤ B → ∃ c : K, c ≠ 0 ∧ c • x ∈ F := by sorry
