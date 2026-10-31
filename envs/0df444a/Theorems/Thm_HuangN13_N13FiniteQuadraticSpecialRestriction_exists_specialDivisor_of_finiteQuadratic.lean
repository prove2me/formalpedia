-- Prove2me | Theorems.Thm_HuangN13_N13FiniteQuadraticSpecialRestriction_exists_specialDivisor_of_finiteQuadratic
-- name    : HuangN13.N13FiniteQuadraticSpecialRestriction.exists_specialDivisor_of_finiteQuadratic
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:30:18.674199+00:00
-- url     : https://prove2.me/theorems/d52ae127-a633-447c-b699-ce6f4e9c4cf4
-- title:
--   exists specialDivisor of finiteQuadratic
-- statement:
--   Exact transplant of the original proof of MazurProof.N13FiniteQuadraticSpecialRestriction.exists_specialDivisor_of_finiteQuadratic from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit9 lines3561–3701, command SHA-256 3afa9b9fdff6c9a9c1d0f4aa6016dd2b9ed9bc7c541e8c982c3ba6e8cd20f33b.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_FiniteInfinityClosureCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore

set_option autoImplicit false
open Polynomial
open Module
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13FiniteQuadraticSpecialRestriction.exists_specialDivisor_of_finiteQuadratic
    (D : MazurProof.SexticMumford.SemiMumford MazurProof.N13FiniteQuadraticSpecialRestriction.Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite MazurProof.N13FiniteQuadraticSpecialRestriction.R₂
        (MazurProof.N13FiniteAffineTwoChart.AffineCurve ⧸
          MazurProof.N13FiniteAffineTwoChart.finiteAffineIdeal D)) :
    ∃ Δ : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo,
      MazurProof.N13TwoChartSpecialRestriction.restrict
          (MazurProof.N13FiniteAffineTwoChart.finiteQuadraticTwoChartLine
            D hdeg hfinite) =
        MazurProof.N13SpecialDivisorCharts.ofDivisor Δ := by sorry
