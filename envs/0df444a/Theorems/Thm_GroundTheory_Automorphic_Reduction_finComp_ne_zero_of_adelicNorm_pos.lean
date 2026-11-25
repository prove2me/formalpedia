-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_finComp_ne_zero_of_adelicNorm_pos
-- name    : GroundTheory.Automorphic.Reduction.finComp_ne_zero_of_adelicNorm_pos
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:03:43.475914+00:00
-- url     : https://prove2.me/theorems/f9ed3843-d31e-54d3-a166-7791b93569e5
-- title:
--   Reduction: fin Comp ne zero of adelic Norm pos
-- statement:
--   The Reduction construction uses the fin Comp ne zero of adelic Norm pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L284-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L284-L293

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

theorem GroundTheory.Automorphic.Reduction.finComp_ne_zero_of_adelicNorm_pos {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (h : 0 < adelicNorm y) (v : HeightOneSpectrum (𝓞 K)) : finComp v y ≠ 0 := by sorry
