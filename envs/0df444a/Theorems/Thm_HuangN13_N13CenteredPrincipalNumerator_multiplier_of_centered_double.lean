-- Prove2me | Theorems.Thm_HuangN13_N13CenteredPrincipalNumerator_multiplier_of_centered_double
-- name    : HuangN13.N13CenteredPrincipalNumerator.multiplier_of_centered_double
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:30:52.586691+00:00
-- url     : https://prove2.me/theorems/9cc51a50-6242-4af1-b9e4-6cfe24c6f1c8
-- title:
--   multiplier of centered double
-- statement:
--   Exact transplant of the original proof of MazurProof.N13CenteredPrincipalNumerator.multiplier_of_centered_double from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines4771–4817, command SHA-256 705eb033807916e0d7040b87578b2e709ac9dc5584eba0355663871b06e87dd9.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DoublingStatementCore

set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13CenteredPrincipalNumerator.multiplier_of_centered_double (P Q : MazurProof.N13CenteredPrincipalNumerator.DiskPair)
    (hc : MazurProof.N13TwoAdicAbelChartPic.DiskPair.centeredPic Q =
      2 • MazurProof.N13TwoAdicAbelChartPic.DiskPair.centeredPic P) :
    ∃ α : MazurProof.N13CenteredPrincipalNumerator.Fˣ,
      MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M P.mumford.toSemi * MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M P.mumford.toSemi *
        toPrincipalIdeal MazurProof.N13CenteredPrincipalNumerator.R MazurProof.N13CenteredPrincipalNumerator.F α = MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M Q.mumford.toSemi *
          MazurProof.SexticMumford.mumfordIdealUnit MazurProof.N13CenteredPrincipalNumerator.M MazurProof.N13CenteredPrincipalNumerator.B.mumford.toSemi ∧
      Multiplicative.toAdd ((MazurProof.N13Infinity.positiveInfinityOrder MazurProof.N13CenteredPrincipalNumerator.K).ordPlus α) = 0 ∧
      Multiplicative.toAdd ((MazurProof.N13InfinityMinus.negativeInfinityOrder MazurProof.N13CenteredPrincipalNumerator.K).ordPlus α) = 0 := by sorry
