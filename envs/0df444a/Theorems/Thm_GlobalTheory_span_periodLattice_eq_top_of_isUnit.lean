-- Prove2me | Theorems.Thm_GlobalTheory_span_periodLattice_eq_top_of_isUnit
-- name    : GlobalTheory.span_periodLattice_eq_top_of_isUnit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:56.686237+00:00
-- url     : https://prove2.me/theorems/07a3e922-d918-4f17-a3ec-ee35023f935b
-- title:
--   Global Theory: span period Lattice eq top of is Unit
-- statement:
--   The Global Theory construction uses the span period Lattice eq top of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L145-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L145-L151

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.span_periodLattice_eq_top_of_isUnit {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) :
    Submodule.span ℝ (periodLattice τ : Set (ι → ℂ)) = ⊤ := by sorry
