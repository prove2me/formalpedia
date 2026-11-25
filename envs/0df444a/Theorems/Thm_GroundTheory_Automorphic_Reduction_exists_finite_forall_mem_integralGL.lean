-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_finite_forall_mem_integralGL
-- name    : GroundTheory.Automorphic.Reduction.exists_finite_forall_mem_integralGL
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:53:22.463856+00:00
-- url     : https://prove2.me/theorems/3dfa23e1-8651-426f-a97f-a41983626717
-- title:
--   Reduction: exists finite forall mem integral GL
-- statement:
--   The Reduction construction uses the exists finite forall mem integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L30-L44

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

theorem GroundTheory.Automorphic.Reduction.exists_finite_forall_mem_integralGL {C : Set (AdelicGLn.AdelicGL K n)} (hC : IsCompact C) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ g ∈ C, ∀ v, v ∉ S →
      finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n := by sorry
