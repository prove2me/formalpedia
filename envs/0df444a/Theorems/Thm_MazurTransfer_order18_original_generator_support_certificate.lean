-- Prove2me | Theorems.Thm_MazurTransfer_order18_original_generator_support_certificate
-- name    : MazurTransfer.order18_original_generator_support_certificate
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T16:13:54.853028+00:00
-- url     : https://prove2.me/theorems/34944b3a-10c5-48ef-81df-e3e3bdf4f12b
-- title:
--   Order18: all four explicit norm-kernel generators are supported above two
-- statement:
--   Let \(K=\mathbb{Q}[T]/(T^3-3T-1)\) and \(M=K[S]/(S^3-3S-10)\). The four explicit compositum elements \(h_1,h_2,h_3,h_4\) have square classes supported at the primes above two: \[v_{\mathfrak p}(h_i)\equiv0\pmod2\quad\text{for every }\mathfrak p\nmid2\text{ and every }i\in\{1,2,3,4\}.\] Thus the published generator-support certificate is inhabited. There is no auxiliary class-number, valuation-certificate or support assumption. This is the concrete support input to the original order-18 descent.
-- source:
--   User WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, original Apache-2.0 headers and attribution retained. The original kernelGeneratorSupportCertificate closure is selected from typed kernel dependencies and complete original Lean AST declaration ranges. Pure certificate data is published separately. All imported rational/relative field and arithmetic interfaces are actually Proved. This is a genuinely smaller arithmetic subproblem after retained 13604-line and 11373-line descent verification timeouts. Named downstream consumer: MazurTransfer.order18_original_quotient_doubling_surjective and the unchanged full rational genus-two campaign exclusion. No custom axioms, proof-strengthening options or new final hypotheses.

import Mathlib
import Definitions.Def_MazurTransfer_Order18KernelGeneratorSupportCertificate

theorem MazurTransfer.order18_original_generator_support_certificate : Nonempty MazurTorsion.XOneEighteenGlobalSelmerBridge.KernelGeneratorSupportCertificate := by sorry
