-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_norm_coeff_minpoly_le_one_of_norm_le_one
-- name    : GlobalTheory.CNorm.norm_coeff_minpoly_le_one_of_norm_le_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:16.413361+00:00
-- url     : https://prove2.me/theorems/80dab4eb-4822-4b54-bc41-05344f802650
-- title:
--   CNorm: norm coeff minpoly le one of norm le one
-- statement:
--   The CNorm construction uses the norm coeff minpoly le one of norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormCoeffMinpolyLeOneOfNormLeOne.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormCoeffMinpolyLeOneOfNormLeOne.lean#L8-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormCoeffMinpolyLeOneOfNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm

theorem GlobalTheory.CNorm.norm_coeff_minpoly_le_one_of_norm_le_one (K : Type) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (L : Type) [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) (h : ‖Algebra.norm K x‖ ≤ 1) (n : ℕ) :
    ‖(minpoly K x).coeff n‖ ≤ 1 := by sorry
