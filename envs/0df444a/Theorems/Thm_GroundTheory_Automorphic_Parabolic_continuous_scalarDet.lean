-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_continuous_scalarDet
-- name    : GroundTheory.Automorphic.Parabolic.continuous_scalarDet
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:16:43.443682+00:00
-- url     : https://prove2.me/theorems/7d1de892-d35f-5555-b3d3-3a851d444afa
-- title:
--   Parabolic: continuous scalar Det
-- statement:
--   The Parabolic construction uses the continuous scalar Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L53-L59

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function Topology ComplexConjugate
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem GroundTheory.Automorphic.Parabolic.continuous_scalarDet : Continuous (scalarDet : GL (Fin n) F → GL (Fin n) F) := by sorry
