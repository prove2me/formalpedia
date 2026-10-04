-- Prove2me | Theorems.Thm_HardyFiveAxioms_real_composite_excess
-- name    : HardyFiveAxioms.real_composite_excess
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T20:17:12.044987+00:00
-- url     : https://prove2.me/theorems/05418f90-8202-4343-8043-c75bb7eeb8e9
-- title:
--   Real Hilbert spaces: composites have more than $K_AK_B$ degrees of freedom
-- statement:
--   Let $K_{\mathbb R}(N)=N+\binom N2=\tfrac12N(N+1)$ be the number of degrees of freedom of real-Hilbert-space quantum theory, i.e. signature $(1,1,0,\dots)$. For all $N_A,N_B\ge2$,
--
--   $$K_{\mathbb R}(N_A)\,K_{\mathbb R}(N_B)<K_{\mathbb R}(N_AN_B).$$
--
--   So real quantum theory violates $K=K_AK_B$ of Axiom 4: some degrees of freedom of a composite can only be measured jointly.
--
--   **Formalization Note** For $N_A=1$ or $N_B=1$ equality holds, which is why both dimensions are taken $\ge2$.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 17, Section 8.1, paragraph on real Hilbert spaces

import Mathlib
import Definitions.Def_hardy2001_signature

namespace HardyFiveAxioms

/-- Hardy 2001, Section 8.1: for real Hilbert spaces (signature `(1, 1, 0, …)`), a composite
system has more degrees of freedom than the product of those of its subsystems. -/
theorem real_composite_excess (NA NB : ℕ) (hA : 2 ≤ NA) (hB : 2 ≤ NB) :
    dofOfSignature [1, 1] NA * dofOfSignature [1, 1] NB < dofOfSignature [1, 1] (NA * NB) := by sorry

end HardyFiveAxioms
