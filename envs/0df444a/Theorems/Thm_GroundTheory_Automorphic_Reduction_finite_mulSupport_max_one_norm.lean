-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_finite_mulSupport_max_one_norm
-- name    : GroundTheory.Automorphic.Reduction.finite_mulSupport_max_one_norm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:20.338433+00:00
-- url     : https://prove2.me/theorems/64439cbd-afb2-4637-bd39-5c755a122cd9
-- title:
--   Reduction: finite mul Support max one norm
-- statement:
--   The Reduction construction uses the finite mul Support max one norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L220-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L220-L225

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Automorphic.Reduction.finite_mulSupport_max_one_norm (s : IdeleGroup K) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => max 1 ‖(s : 𝔸[K]).2 v‖).Finite := by sorry
