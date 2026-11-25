-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_isOpen_setOf_forall_not_mem_imp
-- name    : GroundTheory.Automorphic.Reduction.isOpen_setOf_forall_not_mem_imp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:04:46.76286+00:00
-- url     : https://prove2.me/theorems/d927b675-bd71-4091-bd34-45bc7e3a89ef
-- title:
--   Reduction: is Open set Of forall not mem imp
-- statement:
--   The Reduction construction uses the is Open set Of forall not mem imp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L21-L28

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

theorem GroundTheory.Automorphic.Reduction.isOpen_setOf_forall_not_mem_imp (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpen {g : AdelicGLn.AdelicGL K n |
      ∀ v, v ∉ S → finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n} := by sorry
