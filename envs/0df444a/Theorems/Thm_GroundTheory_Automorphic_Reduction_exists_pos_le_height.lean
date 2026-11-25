-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_pos_le_height
-- name    : GroundTheory.Automorphic.Reduction.exists_pos_le_height
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:04:01.121856+00:00
-- url     : https://prove2.me/theorems/87a17a7b-dc65-4951-ab57-95cd190fa8a1
-- title:
--   Reduction: exists pos le height
-- statement:
--   The Reduction construction uses the exists pos le height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L133-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L133-L192

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

theorem GroundTheory.Automorphic.Reduction.exists_pos_le_height {C : Set (AdelicGLn.AdelicGL K n)} (hC : IsCompact C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ C, ∀ x : Fin n → K, x ≠ 0 → ε ≤ height g x := by sorry
