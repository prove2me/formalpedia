-- Prove2me | Theorems.Thm_HuangN13_N13IrreducibleQuadraticSpread_exists_reciprocalGraphClosure_or_verticalGraph
-- name    : HuangN13.N13IrreducibleQuadraticSpread.exists_reciprocalGraphClosure_or_verticalGraph
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:35:22.099508+00:00
-- url     : https://prove2.me/theorems/582dd3e4-00a7-4714-ac7c-fca38dcef482
-- title:
--   exists reciprocalGraphClosure or verticalGraph
-- statement:
--   Exact transplant of the original proof of MazurProof.N13IrreducibleQuadraticSpread.exists_reciprocalGraphClosure_or_verticalGraph from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit9 lines11692–11727, command SHA-256 9842348fba67599b0f45eb73b7099b8d558bb4b1ab52a4c91be79dc29131244a.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_InfinityGraphLineCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13IrreducibleQuadraticSpread.exists_reciprocalGraphClosure_or_verticalGraph
    (D : MazurProof.SexticMumford.Mumford MazurProof.N13IrreducibleQuadraticSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : MazurProof.N13IrreducibleQuadraticSpread.R₂)
    (hm :
      (X ^ 2 + C (a : MazurProof.N13IrreducibleQuadraticSpread.Q₂) * X + C (b : MazurProof.N13IrreducibleQuadraticSpread.Q₂) : MazurProof.N13IrreducibleQuadraticSpread.Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    Nonempty (MazurProof.N13IrreducibleQuadraticSpread.ReciprocalGraphClosure D a b) ∨
      (∃ E :
          MazurProof.N13IntegralInfinityVerticalGraphJacobian.VerticalGraph,
        E.m.natDegree = 2 ∧
        MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal
            D hdeg h0 =
          E.ideal) := by sorry
