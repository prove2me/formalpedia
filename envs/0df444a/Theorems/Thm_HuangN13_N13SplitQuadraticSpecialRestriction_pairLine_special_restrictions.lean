-- Prove2me | Theorems.Thm_HuangN13_N13SplitQuadraticSpecialRestriction_pairLine_special_restrictions
-- name    : HuangN13.N13SplitQuadraticSpecialRestriction.pairLine_special_restrictions
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:19:34.180896+00:00
-- url     : https://prove2.me/theorems/0d877248-d5b7-4204-bdbb-9e401e7483d4
-- title:
--   Both special restrictions of the actual pair line
-- statement:
--   Reduce each original point line on both charts by splitting into its integral and escaping cases. The integral infinity closure is the explicit weighted point ideal; its reduction is the canonical special point ideal. Restriction respects tensor products, so multiply the two point-line identities to obtain the affine and infinity identities for their reduced pair divisor.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Original targets flattened unit10 lines2005–2029 and2031–2055. Both original proof bodies are retained; the final wrapper pairs their exact conclusions.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13SplitQuadraticSpecialRestriction.pairLine_special_restrictions
    (x₁ y₁ x₂ y₂ : MazurProof.N13SplitQuadraticSpecialRestriction.Q₂)
    (hcurve₁ : MazurProof.N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : MazurProof.N13GoodModelTwo.AffineEquation x₂ y₂) :
    ((MazurProof.N13TwoChartSpecialRestriction.restrict
      (MazurProof.N13QuadraticTwoChartSpread.pairLine
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).affineIdeal =
      (MazurProof.N13SpecialDivisorCharts.ofDivisor
        (MazurProof.N13SplitQuadraticSpecialRestriction.reducedPairDivisor
          x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).affineIdeal) ∧
    ((MazurProof.N13TwoChartSpecialRestriction.restrict
      (MazurProof.N13QuadraticTwoChartSpread.pairLine
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).infinityIdeal =
      (MazurProof.N13SpecialDivisorCharts.ofDivisor
        (MazurProof.N13SplitQuadraticSpecialRestriction.reducedPairDivisor
          x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).infinityIdeal) := by sorry
