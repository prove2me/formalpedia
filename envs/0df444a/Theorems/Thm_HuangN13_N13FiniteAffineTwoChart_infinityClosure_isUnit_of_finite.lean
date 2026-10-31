-- Prove2me | Theorems.Thm_HuangN13_N13FiniteAffineTwoChart_infinityClosure_isUnit_of_finite
-- name    : HuangN13.N13FiniteAffineTwoChart.infinityClosure_isUnit_of_finite
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T11:45:22.030977+00:00
-- url     : https://prove2.me/theorems/a9d8d88c-3152-48b4-9a20-94a479f0ab8f
-- title:
--   Finite invertible affine ideals have invertible infinity closure
-- statement:
--   Finite affine support supplies a monic relation. Reflecting that relation makes the infinity coordinate a unit modulo the contracted ideal. Affine invertibility transfers to the overlap; the localization patching lemma then gives invertibility on the whole infinity chart. Finally transport through the canonical fraction-field equivalence.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit8 lines8786–8882, command SHA-256 697b8805268911e19070614935c114fb80e0ec0ec3797662ecff1653511c2432.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_FiniteInfinityClosureCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13FiniteAffineTwoChart.infinityClosure_isUnit_of_finite
    (I : Ideal MazurProof.N13FiniteAffineTwoChart.AffineCurve)
    (hI : IsUnit (I : MazurProof.N13FiniteAffineTwoChart.AffineFractionalIdeal))
    (hfinite :
      Module.Finite MazurProof.N13FiniteAffineTwoChart.R₂ (MazurProof.N13FiniteAffineTwoChart.AffineCurve ⧸ I)) :
    IsUnit
      (MazurProof.N13FiniteAffineTwoChart.infinityClosure I : MazurProof.N13FiniteAffineTwoChart.InfinityFractionalIdeal) := by sorry
