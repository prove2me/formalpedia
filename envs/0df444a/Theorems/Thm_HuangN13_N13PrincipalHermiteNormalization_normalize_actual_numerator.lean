-- Prove2me | Theorems.Thm_HuangN13_N13PrincipalHermiteNormalization_normalize_actual_numerator
-- name    : HuangN13.N13PrincipalHermiteNormalization.normalize_actual_numerator
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:30:59.963562+00:00
-- url     : https://prove2.me/theorems/6f5d4a33-bc7c-4a3d-adf9-9b4489ca13e9
-- title:
--   normalize actual numerator
-- statement:
--   Exact transplant of the original proof of MazurProof.N13PrincipalHermiteNormalization.normalize_actual_numerator from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines5562–5589, command SHA-256 974f75f0038286bdd9f158ad70222317f33da87b1746b2eae77fcebc9f6df6d9.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DoublingStatementCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13PrincipalHermiteNormalization.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13PrincipalHermiteNormalization.normalize_actual_numerator (P Q : MazurProof.N13CenteredPrincipalNumerator.DiskPair) (n : MazurProof.N13CenteredPrincipalNumerator.R) (A b : MazurProof.N13CenteredPrincipalNumerator.K[X])
    (hn : n ≠ 0) (hA : A.natDegree ≤ 2) (hb : b.natDegree ≤ 1)
    (hshape : MazurProof.N13GoodCenteredNumerator.toGood n = MazurProof.N13GoodCenteredNumerator.gx ((X ^ 2 + X) * A) + MazurProof.N13GoodCenteredNumerator.gx b * MazurProof.N13GoodCenteredNumerator.gy)
    (hmem : n ∈ (MazurProof.SexticMumford.mumfordIdeal MazurProof.N13CenteredPrincipalNumerator.M Q.mumford.u Q.mumford.v *
        MazurProof.SexticMumford.mumfordIdeal MazurProof.N13CenteredPrincipalNumerator.M MazurProof.N13CenteredPrincipalNumerator.B.mumford.u MazurProof.N13CenteredPrincipalNumerator.B.mumford.v) *
      (MazurProof.SexticMumford.mumfordIdeal MazurProof.N13CenteredPrincipalNumerator.M (MazurProof.SexticMumford.conjugateSemiMumford MazurProof.N13CenteredPrincipalNumerator.M P.mumford.toSemi).u
        (MazurProof.SexticMumford.conjugateSemiMumford MazurProof.N13CenteredPrincipalNumerator.M P.mumford.toSemi).v) ^ 2) :
    ∃ t : MazurProof.N13CenteredPrincipalNumerator.K, ∃ d₀ d₁ e₀ e₁ : ℤ_[2],
      t ≠ 0 ∧
      A = C t * (MazurProof.N13HermiteResidualDivisibility.quad d₀ d₁).map MazurProof.N13ActualHermiteEquations.c ∧
      b = C t * (MazurProof.N13HermiteResidualDivisibility.lin e₀ e₁).map MazurProof.N13ActualHermiteEquations.c ∧
      e₀ ∈ MazurProof.N13CenteredHermiteFirstOrder.I P * MazurProof.N13CenteredHermiteFirstOrder.I P ∧
      e₁ ∈ MazurProof.N13CenteredHermiteFirstOrder.I P * MazurProof.N13CenteredHermiteFirstOrder.I P ∧
      d₀ - 2 * P.x₀ * P.x₁ ∈
        MazurProof.N13CenteredHermiteFirstOrder.I P * MazurProof.N13CenteredHermiteFirstOrder.I P ∧
      d₁ + 2 * (P.x₀ + P.x₁) + 1 ∈
        MazurProof.N13CenteredHermiteFirstOrder.I P * MazurProof.N13CenteredHermiteFirstOrder.I P := by sorry
