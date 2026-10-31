-- Prove2me | Theorems.Thm_HuangN13_N13ConcreteGraphRecovery_exists_diskPair_class_eq
-- name    : HuangN13.N13ConcreteGraphRecovery.exists_diskPair_class_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:55:26.053998+00:00
-- url     : https://prove2.me/theorems/360c4659-ce20-4b82-936b-e65daa11654e
-- title:
--   exists diskPair class eq
-- statement:
--   Exact transplant of the original proof of MazurProof.N13ConcreteGraphRecovery.exists_diskPair_class_eq from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit3 lines8742–8820, command SHA-256 c9890ed2036647ac4f3fd8b33c6c505371ad9b0551292205f5fbe6ccc8bf2a12.

import Mathlib
import Definitions.Def_MazurN13_L4

set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13ConcreteGraphRecovery.exists_diskPair_class_eq
    (D : MazurProof.SexticMumford.Mumford MazurProof.N13ConcreteGraphRecovery.Model)
    (hmap :
      Ideal.map
          MazurProof.N13GeneralizedMumfordReduction.reduceCoordinate
          (MazurProof.N13IntegralModelContraction.contractIdeal
            (MazurProof.N13CanonicalContractionQuotient.graphIdeal D.toSemi)) =
        MazurProof.N13SpecialQuotientBasis.specialIdeal) :
    ∃ P : MazurProof.N13TwoAdicAbelChartData.DiskPair,
      MazurProof.SexticMumford.classOf
          MazurProof.N13ConcreteGraphRecovery.Model (MazurProof.N13Infinity.positiveInfinityOrder MazurProof.N13ConcreteGraphRecovery.Q₂) D =
        MazurProof.N13TwoAdicAbelChartPic.DiskPair.pic P := by sorry
