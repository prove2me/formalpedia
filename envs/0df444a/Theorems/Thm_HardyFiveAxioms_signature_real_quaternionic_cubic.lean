-- Prove2me | Theorems.Thm_HardyFiveAxioms_signature_real_quaternionic_cubic
-- name    : HardyFiveAxioms.signature_real_quaternionic_cubic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T19:34:06.397841+00:00
-- url     : https://prove2.me/theorems/7bf6598d-b1d5-4b19-997b-2a4c1e6f88d5
-- title:
--   Signatures of real, quaternionic and $K=N^3$ theories
-- statement:
--   For every $N\in\mathbb N$:
--
--   1. the real-Hilbert-space signature $(1,1,0,\dots)$ gives $K=N+\binom N2=\tfrac12N(N+1)$;
--   2. the quaternionic signature $(1,4,0,\dots)$ gives $K=N+4\binom N2=2N^2-N$;
--   3. the signature $(1,6,6,0,\dots)$ gives $K=N+6\binom N2+6\binom N3=N^3$.
--
--   In Lean these read $2K_{(1,1)}(N)=N(N+1)$, $K_{(1,4)}(N)+N=2N^2$ and $K_{(1,6,6)}(N)=N^3$.
--
--   **Formalization Note** The forms $2K=N(N+1)$ and $K+N=2N^2$ avoid natural-number division and subtraction.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 8, Section 5 (after Eq. (28)); p. 17, Section 8.1 (real and quaternionic Hilbert spaces, $K=N^3$)

import Mathlib
import Definitions.Def_hardy2001_signature

namespace HardyFiveAxioms

/-- Hardy 2001, Sections 5 and 8.1: the real-Hilbert-space signature `(1, 1, 0, …)` gives
`K = N(N+1)/2`, the quaternionic signature `(1, 4, 0, …)` gives `K = 2N² - N`, and the
signature `(1, 6, 6, 0, …)` gives `K = N³`. -/
theorem signature_real_quaternionic_cubic (N : ℕ) :
    2 * dofOfSignature [1, 1] N = N * (N + 1) ∧
      dofOfSignature [1, 4] N + N = 2 * N ^ 2 ∧
      dofOfSignature [1, 6, 6] N = N ^ 3 := by sorry

end HardyFiveAxioms
