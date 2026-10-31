-- Prove2me | Theorems.Thm_HuangN13_N13RankTwoSemiGraphRecovery_exists_integral_semiGraph_of_basis
-- name    : HuangN13.N13RankTwoSemiGraphRecovery.exists_integral_semiGraph_of_basis
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:12:50.991597+00:00
-- url     : https://prove2.me/theorems/80f2eadb-2e92-4a6b-8feb-acad1e2b30f3
-- title:
--   exists integral semiGraph of basis
-- statement:
--   Exact transplant of the original proof of MazurProof.N13RankTwoSemiGraphRecovery.exists_integral_semiGraph_of_basis from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit3 lines10001–10146, command SHA-256 a451230d65915c6e6006bfd87e2f4405a5b1b2eb7f70b13ddabf2004494dd9b0.

import Mathlib
import Definitions.Def_MazurN13_L4

set_option autoImplicit false
open Polynomial
open Module
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13RankTwoSemiGraphRecovery.exists_integral_semiGraph_of_basis
    (D : MazurProof.SexticMumford.SemiMumford MazurProof.N13RankTwoSemiGraphRecovery.Model)
    (b : Basis (Fin 2) MazurProof.N13RankTwoSemiGraphRecovery.R₂
      (MazurProof.N13RankTwoSemiGraphRecovery.IntegralRing ⧸
        MazurProof.N13IntegralModelContraction.contractIdeal
          (MazurProof.N13CanonicalContractionQuotient.graphIdeal D)))
    (hb :
      (b : Fin 2 →
        MazurProof.N13RankTwoSemiGraphRecovery.IntegralRing ⧸
          MazurProof.N13IntegralModelContraction.contractIdeal
            (MazurProof.N13CanonicalContractionQuotient.graphIdeal D)) =
        MazurProof.N13TwoFiberNoEscape.pairFamily
          1
          (Ideal.Quotient.mk
            (MazurProof.N13IntegralModelContraction.contractIdeal
              (MazurProof.N13CanonicalContractionQuotient.graphIdeal D))
            MazurProof.N13CanonicalContractionQuotient.integralX)) :
    ∃ E : MazurProof.N13RankTwoSemiGraphRecovery.SemiMumford₂,
      E.u.natDegree = 2 ∧
      MazurProof.N13IntegralModelContraction.contractIdeal
          (MazurProof.N13CanonicalContractionQuotient.graphIdeal D) =
        MazurProof.N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := MazurProof.N13RankTwoSemiGraphRecovery.R₂) E.u E.v := by sorry
