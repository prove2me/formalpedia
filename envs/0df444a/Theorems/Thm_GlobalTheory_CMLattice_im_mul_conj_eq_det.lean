-- Prove2me | Theorems.Thm_GlobalTheory_CMLattice_im_mul_conj_eq_det
-- name    : GlobalTheory.CMLattice.im_mul_conj_eq_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:55.640827+00:00
-- url     : https://prove2.me/theorems/2dd528e8-4aa4-4f0b-9504-37f11f76a516
-- title:
--   CMLattice: im mul conj eq det
-- statement:
--   The CMLattice construction uses the im mul conj eq det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeCmEqIdealAndCovolume.lean#L101-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeCmEqIdealAndCovolume.lean#L101-L113

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
open GlobalTheory.CMLattice
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.CMLattice.im_mul_conj_eq_det (σ : K →+* ℂ) (b : Basis (Fin 2) ℚ K) (v : Fin 2 → K) :
    (σ (v 0) * starRingEnd ℂ (σ (v 1))).im =
      (b.det v : ℚ) * (σ (b 0) * starRingEnd ℂ (σ (b 1))).im := by sorry
