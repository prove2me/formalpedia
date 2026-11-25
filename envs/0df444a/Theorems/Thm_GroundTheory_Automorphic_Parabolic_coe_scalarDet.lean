-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_coe_scalarDet
-- name    : GroundTheory.Automorphic.Parabolic.coe_scalarDet
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:09:18.889637+00:00
-- url     : https://prove2.me/theorems/cf5c455a-5eb1-50dc-8a23-80c895c9bb47
-- title:
--   Parabolic: coe scalar Det
-- statement:
--   The Parabolic construction uses the coe scalar Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L33-L35

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

theorem GroundTheory.Automorphic.Parabolic.coe_scalarDet (g : GL (Fin n) F) :
    ((scalarDet g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.scalar (Fin n) (g : Matrix (Fin n) (Fin n) F).det := by sorry
