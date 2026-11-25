-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_HasCentralChar_mul
-- name    : GroundTheory.Automorphic.Parabolic.HasCentralChar.mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:47:23.953025+00:00
-- url     : https://prove2.me/theorems/4fea53cf-505b-5862-af58-ccaea3d7950f
-- title:
--   Has Central Char: mul
-- statement:
--   The Has Central Char construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingCoeff.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingCoeff.lean#L33-L38

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingSums
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
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
open Function
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {U : Type*} [AddCommGroup U] [Module ℂ U]
variable {ρ : Representation ℂ (GL (Fin n) F) U} {ω : GL (Fin n) F → ℂ}
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.Parabolic.HasCentralChar.mul (h : HasCentralChar ρ ω) {u : U} (hu : u ≠ 0)
    {z z' : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F))
    (hz' : z' ∈ Subgroup.center (GL (Fin n) F)) : ω (z * z') = ω z * ω z' := by sorry
