-- Prove2me | Theorems.Thm_HuangN13_N13ReciprocalGraphPicardRealization_horizontalGraph_saturated_and_marked
-- name    : HuangN13.N13ReciprocalGraphPicardRealization.horizontalGraph_saturated_and_marked
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:42:49.093895+00:00
-- url     : https://prove2.me/theorems/d8847864-b238-4b1b-9a46-4d6e583046a1
-- title:
--   Actual reciprocal graph lines are saturated and correctly infinity-marked
-- statement:
--   For an actual reciprocal graph closure, identify its generic Mumford ideal and transport scalar saturation from the original contracted ideal to the integral affine lattice. On the infinity branches, the reciprocal polynomial has nonzero constant coefficient, so its image is a unit power series and the graph ideal has zero multiplicity. Pair the two original universally quantified statements without changing their binder lists or the proofs used inside the actual graph-line arguments.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Exact original target owner ranges and SHA-256s are recorded in metadata.json. The first source declaration has the qualified name ReciprocalGraphClosure.twoChartLine_affineVerticallySaturated; the recorded Stage2 name token is used verbatim.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_InfinityGraphLineCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_ReciprocalPolynomialFactsCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13ReciprocalGraphPicardRealization.horizontalGraph_saturated_and_marked :
    (∀
    {D : MazurProof.SexticMumford.Mumford
      MazurProof.N13IrreducibleQuadraticSpread.Model}
    {a b : MazurProof.N13IrreducibleQuadraticSpread.R₂}
    (E : MazurProof.N13IrreducibleQuadraticSpread.ReciprocalGraphClosure D a b),
MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated
      (MazurProof.N13IntegralInfinityGraphTwoChart.twoChartLine
        E.data (by
          rw [E.data_u]
          exact
            (MazurProof.N13ReciprocalQuadraticReflection.integralReciprocal_natDegree
              a b).le) E.v_degree E.w_degree (by
          rw [E.data_u]
          exact
            (MazurProof.N13ReciprocalQuadraticReflection.integralReciprocal_monic
              a b).ne_zero))) ∧
    (∀
    (D : MazurProof.N13IntegralInfinityGraphTwoChart.GraphData)
    (hu : D.u.natDegree ≤ 2) (hv : D.v.natDegree ≤ 3) (hw : D.w.natDegree ≤ 4)
    (hne : D.u ≠ 0)
    (h0 : MazurProof.N13TwoAdicInfinityCompatibility.coeffMap (D.u.coeff 0) ≠ 0),
MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities
      (MazurProof.N13IntegralInfinityGraphTwoChart.twoChartLine D hu hv hw hne) 0 0) := by sorry
