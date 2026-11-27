-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_iwasawa_decomposition
-- name    : GroundTheory.Automorphic.iwasawa_decomposition
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:51.875093+00:00
-- url     : https://prove2.me/theorems/3793e37e-9434-4b36-8a39-80a0df6f5862
-- title:
--   Automorphic: iwasawa decomposition
-- statement:
--   The Automorphic construction uses the iwasawa decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsIwasawa.lean#L463-L470
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsIwasawa.lean#L463-L470

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

theorem GroundTheory.Automorphic.iwasawa_decomposition (g : GL n 𝕜) :
    ∃! x : unitaryGroup n 𝕜 × PosDiag n × UpperUnitriangular n 𝕜,
      (x.1 : Matrix n n 𝕜) * diagonal (fun i => (x.2.1.1 i : 𝕜)) * x.2.2.1 = g := by sorry
