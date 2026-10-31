-- Prove2me | Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_supported_small_function_certificate
-- name    : HuangN13.N13SpecialSmallFunctionCertificate.supported_small_function_certificate
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:25:00.611231+00:00
-- url     : https://prove2.me/theorems/9bfee99b-2e4c-489e-aae5-a1925d824dbe
-- title:
--   The supported N13 small-function certificate
-- statement:
--   For every numerator coefficient vector in F₂⁵ and ordinate coefficient vector in F₂², norm support dividing X¹⁶(X−1)¹⁶ forces the six prescribed jets to satisfy their nonvanishing-order certificates and zero weighted code modulo19.
-- source:
--   Xiang Huang, Apache-2.0. Original source: https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/N13SpecialSmallFunctionCertificate.lean; exact flattened unit18 lines798-952. The original proof body is preserved after sixteen conjunction eliminations bind its original128 row names. Original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore

set_option autoImplicit false

theorem HuangN13.N13SpecialSmallFunctionCertificate.supported_small_function_certificate : ∀ (a : Fin 5 → MazurProof.N13SpecialSmallFunctionCertificate.K) (b : Fin 2 → MazurProof.N13SpecialSmallFunctionCertificate.K), MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate a b := by sorry
