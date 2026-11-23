-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_coe_iwasawaHomeomorph_apply
-- name    : GroundTheory.Automorphic.coe_iwasawaHomeomorph_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:55.794454+00:00
-- url     : https://prove2.me/theorems/4dd9d23a-4f49-4e1f-ad50-c37687a0bdc1
-- title:
--   Automorphic: coe iwasawa Homeomorph apply
-- statement:
--   The Automorphic construction uses the coe iwasawa Homeomorph apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsIwasawa.lean#L458-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsIwasawa.lean#L458-L461

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix
open scoped ComplexOrder
set_option linter.unusedSectionVars false
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]
open scoped Matrix.Norms.L2Operator Topology
open Filter Set
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem GroundTheory.Automorphic.coe_iwasawaHomeomorph_apply
    (x : unitaryGroup n 𝕜 × PosDiag n × UpperUnitriangular n 𝕜) :
    ((iwasawaHomeomorph x : GL n 𝕜) : Matrix n n 𝕜) =
      (x.1 : Matrix n n 𝕜) * diagonal (fun i => (x.2.1.1 i : 𝕜)) * x.2.2.1 := by sorry

attribute [defeq] GroundTheory.Automorphic.coe_iwasawaHomeomorph_apply
