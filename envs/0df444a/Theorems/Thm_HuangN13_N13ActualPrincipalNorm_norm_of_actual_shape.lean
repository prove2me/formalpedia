-- Prove2me | Theorems.Thm_HuangN13_N13ActualPrincipalNorm_norm_of_actual_shape
-- name    : HuangN13.N13ActualPrincipalNorm.norm_of_actual_shape
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:30:38.285984+00:00
-- url     : https://prove2.me/theorems/2e6e8f90-0af9-4852-a99c-2f291dc89c04
-- title:
--   norm of actual shape
-- statement:
--   Exact transplant of the original proof of MazurProof.N13ActualPrincipalNorm.norm_of_actual_shape from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines5688–5710, command SHA-256 9e307276b85732aa9334cbd1295dff840591ed5eb12718748306d30af390ab30.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DoublingStatementCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13ActualPrincipalNorm.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13ActualPrincipalNorm.norm_of_actual_shape (P Q : MazurProof.N13CenteredPrincipalNumerator.DiskPair) (α : MazurProof.N13CenteredPrincipalNumerator.Fˣ) (n : MazurProof.N13CenteredPrincipalNumerator.R) (A b : MazurProof.N13CenteredPrincipalNumerator.K[X])
    (h : MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M P.mumford.toSemi * MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M P.mumford.toSemi *
      toPrincipalIdeal MazurProof.N13CenteredPrincipalNumerator.R MazurProof.N13CenteredPrincipalNumerator.F α = MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M Q.mumford.toSemi *
        MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M MazurProof.N13CenteredPrincipalNumerator.B.mumford.toSemi)
    (hn : algebraMap MazurProof.N13CenteredPrincipalNumerator.R MazurProof.N13CenteredPrincipalNumerator.F n = (α : MazurProof.N13CenteredPrincipalNumerator.F) * algebraMap MazurProof.N13CenteredPrincipalNumerator.R MazurProof.N13CenteredPrincipalNumerator.F (MazurProof.SexticMumford.xClass MazurProof.N13CenteredPrincipalNumerator.M (P.mumford.u ^ 2)))
    (hshape : MazurProof.N13GoodCenteredNumerator.toGood n = MazurProof.N13GoodCenteredNumerator.gx ((X ^ 2 + X) * A) + MazurProof.N13GoodCenteredNumerator.gx b * MazurProof.N13GoodCenteredNumerator.gy) :
    ∃ k : MazurProof.N13CenteredPrincipalNumerator.Kˣ,
      ((X ^ 2 + X) * A) ^ 2 - ((X ^ 2 + X) * A) * b *
          MazurProof.N13GeneralizedMumfordIntegral.hPoly - b ^ 2 * MazurProof.N13GeneralizedMumfordIntegral.rhsPoly =
        C (k : MazurProof.N13CenteredPrincipalNumerator.K) * (MazurProof.N13TwoAdicMumfordTransport.mapPoly P.u) ^ 2 *
          (X ^ 2 + X) * MazurProof.N13TwoAdicMumfordTransport.mapPoly Q.u := by sorry
