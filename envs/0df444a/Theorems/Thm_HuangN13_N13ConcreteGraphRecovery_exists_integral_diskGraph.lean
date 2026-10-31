-- Prove2me | Theorems.Thm_HuangN13_N13ConcreteGraphRecovery_exists_integral_diskGraph
-- name    : HuangN13.N13ConcreteGraphRecovery.exists_integral_diskGraph
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:49:49.364701+00:00
-- url     : https://prove2.me/theorems/17163a66-29ec-4f23-ad5f-34befe725569
-- title:
--   exists integral diskGraph
-- statement:
--   Exact transplant of the original proof of MazurProof.N13ConcreteGraphRecovery.exists_integral_diskGraph from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit3 lines8687–8740, command SHA-256 d097953d600be7242ebc4ae47428fdaed45663807ab661768b9a67627f604bb5.

import Mathlib
import Definitions.Def_MazurN13_L4

set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13ConcreteGraphRecovery.exists_integral_diskGraph
    (D : MazurProof.SexticMumford.SemiMumford MazurProof.N13ConcreteGraphRecovery.Model)
    (hdeg : D.u.natDegree = 2)
    (hmap :
      Ideal.map
          MazurProof.N13GeneralizedMumfordReduction.reduceCoordinate
          (MazurProof.N13IntegralModelContraction.contractIdeal
            (MazurProof.N13CanonicalContractionQuotient.graphIdeal D)) =
        MazurProof.N13SpecialQuotientBasis.specialIdeal) :
    ∃ E : MazurProof.N13ConcreteGraphRecovery.SmoothMumford₂,
      ∃ P : MazurProof.N13TwoAdicAbelChartData.DiskPair,
        E.u.natDegree = 2 ∧
        MazurProof.N13CanonicalContractionQuotient.graphIdeal D =
          MazurProof.N13IntegralGraphContraction.sexticIdeal E D.nInf ∧
        MazurProof.N13GeneralizedMumfordIntegral.mumfordIdeal E.u E.v =
          MazurProof.N13GeneralizedMumfordIntegral.mumfordIdeal P.u P.v := by sorry
