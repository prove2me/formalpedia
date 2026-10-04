-- Prove2me | Theorems.Thm_HardyFiveAxioms_signature_classical_quantum
-- name    : HardyFiveAxioms.signature_classical_quantum
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T18:12:12.510456+00:00
-- url     : https://prove2.me/theorems/309b961c-af7c-4e48-bf79-50bc8fd9a815
-- title:
--   Signatures $(1,0,\dots)$ and $(1,2,0,\dots)$ give $K=N$ and $K=N^2$
-- statement:
--   For every $N\in\mathbb N$, with $K_x(N)=\sum_k\binom Nkx_k$ as in `hardy2001_signature`:
--
--   $$K_{(1)}(N)=N,\qquad K_{(1,2)}(N)=N+2\binom N2=N^2 .$$
--
--   These are the classical signature $x_{\rm Classical}=(1,0,0,\dots)$ and the quantum signature $x_{\rm Quantum}=(1,2,0,0,\dots)$ of Section 5.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 8, Section 5, Eq. (28) and the following sentence

import Mathlib
import Definitions.Def_hardy2001_signature

namespace HardyFiveAxioms

/-- Hardy 2001, Section 5 (after Eq. (28)): the classical signature `(1, 0, 0, …)` gives
`K = N` and the quantum signature `(1, 2, 0, 0, …)` gives `K = N²`. -/
theorem signature_classical_quantum (N : ℕ) :
    dofOfSignature [1] N = N ∧ dofOfSignature [1, 2] N = N ^ 2 := by sorry

end HardyFiveAxioms
