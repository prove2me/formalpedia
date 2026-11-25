-- Prove2me | Theorems.Thm_GlobalTheory_IsLatticeFrame_finite_quotient
-- name    : GlobalTheory.IsLatticeFrame.finite_quotient
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:13.411104+00:00
-- url     : https://prove2.me/theorems/af2555de-7989-55a2-b2a6-274c21041805
-- title:
--   Is Lattice Frame: finite quotient
-- statement:
--   The Is Lattice Frame construction uses the finite quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L659-L661
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L659-L661

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
open GlobalTheory.IsLatticeFrame
variable {A : Submodule (𝓞 K) V} {ι κ : Type*} {e : ι → V}

theorem GlobalTheory.IsLatticeFrame.finite_quotient (he : IsLatticeFrame A e) (hA : A.FG) :
    Finite (A ⧸ (Submodule.span (𝓞 K) (Set.range e)).submoduleOf A) := by sorry
