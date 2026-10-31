-- Prove2me | Theorems.Thm_ObliviousRSP_trace_mul_partialTraceRight
-- name    : ObliviousRSP.trace_mul_partialTraceRight
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:09.717989+00:00
-- url     : https://prove2.me/theorems/63791213-8edf-405a-a197-c8743606c4d7
-- title:
--   Identity $\operatorname{Tr}(A\,\operatorname{Tr}_2 B_{12}) = \operatorname{Tr}((A\otimes I)B)$
-- statement:
--   For every square matrix $A$ on a finite-dimensional space $\mathcal H_1$ and every operator $B$ on $\mathcal H_1\otimes\mathcal H_2$,
--   $$
--   \operatorname{Tr}\big(A\,(\operatorname{Tr}_2 B_{12})\big) = \operatorname{Tr}\big((A\otimes I)\,B\big),
--   $$
--   where $\operatorname{Tr}_2$ is the partial trace over the second factor.
--
--   The paper uses it to obtain (10) and (12).
--
--   **Formalization Note** $\operatorname{Tr}_2$ is `WildeQIT.partialTraceRight`; both factors are arbitrary finite index types.
--
--   Differences from the source: none.
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, p.4, identity used for eqs. (10) and (12)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace

open scoped Kronecker

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, p.4, the identity used for eqs. (10) and (12): "Tr ( A (Tr2B12) ) = Tr ( (A ⊗ I) B )".
For a square matrix `A` on the first factor and `B` on the product of the two factors,
`Tr(A · Tr_2 B) = Tr((A ⊗ I) B)`.

**Formalization Note.** `Tr_2` (the second tensor component) is `WildeQIT.partialTraceRight`; the
factors are arbitrary finite types. -/
theorem trace_mul_partialTraceRight {a c : Type} [Fintype a] [Fintype c] [DecidableEq c]
    (A : Matrix a a ℂ) (B : Matrix (a × c) (a × c) ℂ) :
    (A * WildeQIT.partialTraceRight B).trace = ((A ⊗ₖ (1 : Matrix c c ℂ)) * B).trace := by sorry

end ObliviousRSP
