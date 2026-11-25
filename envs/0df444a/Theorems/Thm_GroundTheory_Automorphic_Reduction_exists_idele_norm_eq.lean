-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_idele_norm_eq
-- name    : GroundTheory.Automorphic.Reduction.exists_idele_norm_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:59.802352+00:00
-- url     : https://prove2.me/theorems/c11bcf19-01af-48b3-9209-b64918b8a762
-- title:
--   Reduction: exists idele norm eq
-- statement:
--   The Reduction construction uses the exists idele norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L250-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L250-L274

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

theorem GroundTheory.Automorphic.Reduction.exists_idele_norm_eq {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (hinf : ∀ w, infComp w y ≠ 0) (hfin : ∀ v, finComp v y ≠ 0) :
    ∃ s : IdeleGroup K, (∀ w, ‖(s : 𝔸[K]).1 w‖ = ‖infComp w y‖) ∧
      ∀ v, ‖(s : 𝔸[K]).2 v‖ = ‖finComp v y‖ := by sorry
