-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_scalarDet_mem_center
-- name    : GroundTheory.Automorphic.Parabolic.scalarDet_mem_center
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:09:24.18536+00:00
-- url     : https://prove2.me/theorems/6798d1ed-0ed7-584b-9fec-c06135b2584e
-- title:
--   Parabolic: scalar Det mem center
-- statement:
--   The Parabolic construction uses the scalar Det mem center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L38-L40

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
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.Parabolic.scalarDet_mem_center (g : GL (Fin n) F) :
    scalarDet g ∈ Subgroup.center (GL (Fin n) F) := by sorry
