-- Prove2me | Theorems.Thm_MazurTransfer_order18_original_kernel_representative_injective
-- name    : MazurTransfer.order18_original_kernel_representative_injective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T15:41:46.235891+00:00
-- url     : https://prove2.me/theorems/a39dbdb6-3361-461f-bfed-cf3028738ced
-- title:
--   Order18: the sixteen explicit global norm-kernel square classes are distinct
-- statement:
--   Let \(K=\mathbb{Q}[T]/(T^3-3T-1)\) and \(M=K[S]/(S^3-3S-10)\). Let \(h_1,h_2,h_3,h_4\in M^\times\) be the four explicit generators in the published compositum data. The sixteen square classes \[\prod_{i=1}^4[h_i]^{e_i}\in M^\times/(M^\times)^2,\qquad(e_1,e_2,e_3,e_4)\in\{0,1\}^4,\] are pairwise distinct. This has no local-solubility or independence hypothesis. It supplies the injectivity input to the global supported norm-kernel enumeration for the order-18 descent.
-- source:
--   User WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The exact original kernelRepresentative_injective closure is selected by typed kernel dependencies and full original Lean AST declaration ranges. The original published coefficient, relative and ambient Selmer data are used coherently, with already-Proved nonzero, normalized cubic and non-square certificates. This is a genuine smaller arithmetic interface after the retained 13604-line doubling-surjectivity verification timeout, not a retry of that source. The named downstream consumer is the unconditional original quotient doubling-surjectivity theorem and ultimately the unchanged rational genus-two campaign exclusion. Original Apache-2.0 headers and attribution preserved. No new mathematical hypotheses, custom axioms or resource-strengthening options.

import Mathlib
import Definitions.Def_MazurTransfer_Order18AmbientSelmer

theorem MazurTransfer.order18_original_kernel_representative_injective : Function.Injective MazurTorsion.XOneEighteenGlobalSelmerBridge.kernelRepresentative := by sorry
