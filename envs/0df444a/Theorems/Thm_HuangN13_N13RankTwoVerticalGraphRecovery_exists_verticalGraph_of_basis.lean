-- Prove2me | Theorems.Thm_HuangN13_N13RankTwoVerticalGraphRecovery_exists_verticalGraph_of_basis
-- name    : HuangN13.N13RankTwoVerticalGraphRecovery.exists_verticalGraph_of_basis
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:12:53.603469+00:00
-- url     : https://prove2.me/theorems/3f006361-bebf-42f7-b3ea-7b446e355cc6
-- title:
--   exists verticalGraph of basis
-- statement:
--   Exact transplant of the original proof of MazurProof.N13RankTwoVerticalGraphRecovery.exists_verticalGraph_of_basis from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit3 lines10684–10825, command SHA-256 15ceeb766aa87d2dc0cfb6386505ff1fa8145cf8467ee1a623398a83f4f35425.

import Mathlib
import Definitions.Def_MazurN13_L4

set_option autoImplicit false
open Polynomial
open Module
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13RankTwoVerticalGraphRecovery.exists_verticalGraph_of_basis
    (D : MazurProof.SexticMumford.SemiMumford MazurProof.N13RankTwoVerticalGraphRecovery.Model)
    (b : Basis (Fin 2) MazurProof.N13RankTwoVerticalGraphRecovery.R₂
      (MazurProof.N13RankTwoVerticalGraphRecovery.IntegralRing ⧸
        MazurProof.N13IntegralModelContraction.contractIdeal
          (MazurProof.N13CanonicalContractionQuotient.graphIdeal D)))
    (hb :
      (b : Fin 2 →
        MazurProof.N13RankTwoVerticalGraphRecovery.IntegralRing ⧸
          MazurProof.N13IntegralModelContraction.contractIdeal
            (MazurProof.N13CanonicalContractionQuotient.graphIdeal D)) =
        MazurProof.N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk
            (MazurProof.N13IntegralModelContraction.contractIdeal
              (MazurProof.N13CanonicalContractionQuotient.graphIdeal D))
            MazurProof.N13ConcreteGraphRecovery.integralY)) :
    ∃ E : MazurProof.N13RankTwoVerticalGraphRecovery.VerticalGraph,
      E.m.natDegree = 2 ∧
      MazurProof.N13IntegralModelContraction.contractIdeal
          (MazurProof.N13CanonicalContractionQuotient.graphIdeal D) =
        E.ideal := by sorry
