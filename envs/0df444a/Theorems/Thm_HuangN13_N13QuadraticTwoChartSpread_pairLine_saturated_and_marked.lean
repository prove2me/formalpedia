-- Prove2me | Theorems.Thm_HuangN13_N13QuadraticTwoChartSpread_pairLine_saturated_and_marked
-- name    : HuangN13.N13QuadraticTwoChartSpread.pairLine_saturated_and_marked
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:20:00.40904+00:00
-- url     : https://prove2.me/theorems/a1811dad-dc4d-4bf6-a9ed-5b687b3eaafd
-- title:
--   Actual point-pair lines are saturated and have zero infinity multiplicities
-- statement:
--   The tensor of two point lines is vertically saturated because each point line is saturated. For the marking, split each point into its integral and escaping presentations: the ordinary finite point has zero order on both infinity branches, and a nonzero inverse coordinate makes the infinity point ideal map to the unit ideal. Multiplicities add under the tensor product. The two original universally quantified results are paired without changing either binder list.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Original targets flattened unit10 lines1874–1891 and6891–6897; both original proof bodies and binder lists are retained.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_FiniteInfinityClosureCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13QuadraticTwoChartSpread.pairLine_saturated_and_marked :
    (∀
    (x₁ y₁ x₂ y₂ : MazurProof.N13QuadraticTwoChartSpread.Q₂)
    (hcurve₁ : MazurProof.N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : MazurProof.N13GoodModelTwo.AffineEquation x₂ y₂),
MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated
      (MazurProof.N13QuadraticTwoChartSpread.pairLine
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)) ∧
    (∀
    (x y z w : MazurProof.N13TwoChartPicardRealization.Q₂)
    (h : MazurProof.N13GoodModelTwo.AffineEquation x y)
    (k : MazurProof.N13GoodModelTwo.AffineEquation z w),
MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities (MazurProof.N13QuadraticTwoChartSpread.pairLine x y z w h k) 0 0) := by sorry
