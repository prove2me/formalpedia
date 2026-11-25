-- Prove2me | Theorems.Thm_GlobalTheory_isLatticeFrame_iff_card_eq
-- name    : GlobalTheory.isLatticeFrame_iff_card_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:02:03.875442+00:00
-- url     : https://prove2.me/theorems/4216a274-cbe5-5258-893e-0bb9e917d7e6
-- title:
--   Global Theory: is Lattice Frame iff card eq
-- statement:
--   The Global Theory construction uses the is Lattice Frame iff card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L704-L712
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L704-L712

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

theorem GlobalTheory.isLatticeFrame_iff_card_eq {A : Submodule (𝓞 K) V} (hA : A.FG) {ι : Type*} [Fintype ι]
    {e : ι → V} : IsLatticeFrame A e ↔
      (∀ i, e i ∈ A) ∧ LinearIndependent K e ∧ Fintype.card ι = finrank (𝓞 K) A := by sorry
