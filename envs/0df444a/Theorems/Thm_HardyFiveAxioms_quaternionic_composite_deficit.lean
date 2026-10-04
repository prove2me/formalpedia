-- Prove2me | Theorems.Thm_HardyFiveAxioms_quaternionic_composite_deficit
-- name    : HardyFiveAxioms.quaternionic_composite_deficit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T21:06:16.02622+00:00
-- url     : https://prove2.me/theorems/5c95217f-9f0d-415a-a1fc-fb2e6fbaf243
-- title:
--   Quaternionic Hilbert spaces: composites have fewer than $K_AK_B$ degrees of freedom
-- statement:
--   Let $K_{\mathbb H}(N)=N+4\binom N2=2N^2-N$ be the number of degrees of freedom of quaternionic quantum theory, i.e. signature $(1,4,0,\dots)$. For all $N_A,N_B\ge2$,
--
--   $$K_{\mathbb H}(N_AN_B)<K_{\mathbb H}(N_A)\,K_{\mathbb H}(N_B).$$
--
--   So quaternionic quantum theory violates $K=K_AK_B$ of Axiom 4.
--
--   **Formalization Note** For $N_A=1$ or $N_B=1$ equality holds.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 17, Section 8.1, paragraph on quaternionic Hilbert spaces

import Mathlib
import Definitions.Def_hardy2001_signature

namespace HardyFiveAxioms

/-- Hardy 2001, Section 8.1: for quaternionic Hilbert spaces (signature `(1, 4, 0, …)`), a
composite system has fewer degrees of freedom than the product of those of its subsystems. -/
theorem quaternionic_composite_deficit (NA NB : ℕ) (hA : 2 ≤ NA) (hB : 2 ≤ NB) :
    dofOfSignature [1, 4] (NA * NB) < dofOfSignature [1, 4] NA * dofOfSignature [1, 4] NB := by sorry

end HardyFiveAxioms
