-- Prove2me | Theorems.Thm_MazurTransfer_order18_original_global_norm_kernel_enumeration
-- name    : MazurTransfer.order18_original_global_norm_kernel_enumeration
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T15:47:06.457553+00:00
-- url     : https://prove2.me/theorems/bc716803-0b47-4369-8fb6-4d151c76cd0e
-- title:
--   Order18: the sixteen explicit classes exhaust the supported relative norm kernel
-- statement:
--   Let \(K=\mathbb{Q}[T]/(T^3-3T-1)\) and \(M=K[S]/(S^3-3S-10)\). In \(M^\times/(M^\times)^2\), restrict to square classes whose valuations are even at every prime not above two. Every such class whose relative norm to \(K\) is a square has the form \[\prod_{i=1}^4[h_i]^{e_i},\qquad(e_1,e_2,e_3,e_4)\in\{0,1\}^4,\] where the four \(h_i\) are the explicit generators in the published compositum data. The support and norm conditions are explicit in the domain of this assertion. No class-number, valuation-certificate or independence assumption is imposed on the fields or generators. The supported relative norm-kernel enumeration is the global input to the unconditional order-18 descent.
-- source:
--   User WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, original Apache-2.0 headers and attribution retained. The complete original dyadicKernelRepresentative_bijective and kernelGeneratorSupportCertificate closures are selected from typed kernel dependencies and complete original Lean AST declaration ranges. Already-Proved arithmetic supplies actual principality, the actual valuation certificate and the supported Selmer cardinality 256. The separately registered sixteen-class injectivity theorem is a tracked child. One coherent original field and ambient Selmer definition family is used. This is a genuine mathematical decomposition of the retained 13604-line original quotient doubling-surjectivity timeout. The named downstream consumer is MazurTransfer.order18_original_quotient_doubling_surjective, with the unchanged full rational genus-two campaign endpoint. No custom axiom, new target hypothesis or proof-strengthening option.

import Mathlib
import Definitions.Def_MazurTransfer_Order18AmbientSelmer

theorem MazurTransfer.order18_original_global_norm_kernel_enumeration (z : MazurTorsion.XOneEighteenGlobalSelmerBridge.fullDyadicRelativeNorm.ker) :
    ∃ mask : Fin 16,
      MazurTorsion.XOneEighteenGlobalSelmerBridge.kernelRepresentative mask =
        ((z : MazurTorsion.XOneEighteenGlobalSelmerBridge.DyadicSelmerM) :
          Units.modPow MazurTorsion.XOneEighteenTwoDivisionArithmetic.M 2) := by sorry
