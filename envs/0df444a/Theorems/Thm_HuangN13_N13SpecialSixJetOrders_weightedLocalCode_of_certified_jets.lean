-- Prove2me | Theorems.Thm_HuangN13_N13SpecialSixJetOrders_weightedLocalCode_of_certified_jets
-- name    : HuangN13.N13SpecialSixJetOrders.weightedLocalCode_of_certified_jets
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:10:00.072537+00:00
-- url     : https://prove2.me/theorems/25f6309e-b730-416c-9664-cf286dc2a76e
-- title:
--   Certified six-branch jets give zero geometric weighted code
-- statement:
--   For a nonzero small numerator with six first-nonzero-coefficient certificates below order nine and zero weighted jet code, the weighted code of its six actual geometric branch orders is zero.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact original compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines3543-3553, source-command SHA-256 ee01ede9487ffa8093731237dc1596e3e4f0e847a42733efe29d1f0ae6c40b26.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialLaurentBranchesCore
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore
import Definitions.Def_HuangN13_SpecialJetCodeCore
import Definitions.Def_HuangN13_SixLocalOrdersCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialSixJetOrders.weightedLocalCode_of_certified_jets (a : Fin 5 → MazurProof.N13SpecialSmallFunctionCertificate.K) (b : Fin 2 → MazurProof.N13SpecialSmallFunctionCertificate.K)
    (hn : MazurProof.N13SpecialSixJetOrders.function a b ≠ 0)
    (hjets : ∀ i : Fin 6, MazurProof.N13SpecialSmallFunctionCertificate.sixJetOrders a b i < 9 ∧
      (MazurProof.N13SpecialSmallFunctionCertificate.sixJetPolynomials a b i).coeff (MazurProof.N13SpecialSmallFunctionCertificate.sixJetOrders a b i) ≠ 0 ∧
      ∀ j : Fin 9, (j : ℕ) < MazurProof.N13SpecialSmallFunctionCertificate.sixJetOrders a b i → (MazurProof.N13SpecialSmallFunctionCertificate.sixJetPolynomials a b i).coeff j = 0)
    (hcode : MazurProof.N13SpecialSmallFunctionCertificate.weightedJetCode a b = 0) : MazurProof.N13SpecialSixJetOrders.weightedLocalCode (MazurProof.N13SpecialSixJetOrders.function a b) = 0 := by sorry
