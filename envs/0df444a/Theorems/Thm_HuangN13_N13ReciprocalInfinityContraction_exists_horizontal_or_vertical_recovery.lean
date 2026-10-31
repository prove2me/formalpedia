-- Prove2me | Theorems.Thm_HuangN13_N13ReciprocalInfinityContraction_exists_horizontal_or_vertical_recovery
-- name    : HuangN13.N13ReciprocalInfinityContraction.exists_horizontal_or_vertical_recovery
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:29:03.022748+00:00
-- url     : https://prove2.me/theorems/28202c2b-a2af-433a-93e9-a64c369a2827
-- title:
--   exists horizontal or vertical recovery
-- statement:
--   Exact transplant of the original proof of MazurProof.N13ReciprocalInfinityContraction.exists_horizontal_or_vertical_recovery from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit9 lines8253–8310, command SHA-256 d8b73c9d2638965c3dc5e0a45597d2b2e8522dbab05f08b9f089005365792274.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_InfinityGraphLineCore
import Definitions.Def_HuangN13_ReciprocalPolynomialFactsCore

set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13ReciprocalInfinityContraction.exists_horizontal_or_vertical_recovery
    (D : MazurProof.SexticMumford.Mumford MazurProof.N13ReciprocalInfinityContraction.Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : MazurProof.N13ReciprocalInfinityContraction.R₂)
    (hm :
      (X ^ 2 + C (a : MazurProof.N13ReciprocalInfinityContraction.Q₂) * X + C (b : MazurProof.N13ReciprocalInfinityContraction.Q₂) : MazurProof.N13ReciprocalInfinityContraction.Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    (∃ E : MazurProof.N13IntegralInfinityGraphTwoChart.GraphData,
      E.u =
        MazurProof.N13ReciprocalQuadraticReflection.integralReciprocal a b ∧
      E.u.Monic ∧
      E.u.natDegree = 2 ∧
      E.v.natDegree ≤ 1 ∧
      E.w.natDegree ≤ 4 ∧
      MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0 =
        MazurProof.N13IntegralInfinityGraphTwoChart.infinityIdeal E ∧
      D.u ∣
        MazurProof.N13GoodSexticMumfordTransport.completedGraph
            (MazurProof.N13TwoAdicCoordinateBaseChange.mapPoly
              (MazurProof.N13IntegralInfinityGraphTwoChart.affineV E)) -
          D.v) ∨
      (∃ E :
          MazurProof.N13IntegralInfinityVerticalGraphJacobian.VerticalGraph,
        E.m.natDegree = 2 ∧
        MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0 = E.ideal) := by sorry
