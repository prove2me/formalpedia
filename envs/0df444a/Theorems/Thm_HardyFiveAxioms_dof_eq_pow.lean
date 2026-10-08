-- Prove2me | Theorems.Thm_HardyFiveAxioms_dof_eq_pow
-- name    : HardyFiveAxioms.dof_eq_pow
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T11:50:35.879215+00:00
-- url     : https://prove2.me/theorems/6e70fc12-2a06-4c83-b762-e4c54d7aae9e
-- title:
--   Hardy's degrees of freedom: $K(N)=N^r$ for a positive integer $r$
-- statement:
--   Let $K$ assign to every dimension $N=1,2,3,\dots$ a number of degrees of freedom $K(N)\in\mathbb N$. Suppose that
--
--   1. $K(N+1)\ge K(N)+1$ for every $N\ge1$, which Hardy derives from the subspace axiom (Axiom 3);
--   2. $K(N_AN_B)=K(N_A)\,K(N_B)$ for all $N_A,N_B\ge1$, which is the composite-systems axiom (Axiom 4).
--
--   Then there is a positive integer $r$ such that
--
--   $$K(N)=N^r\qquad\text{for all }N\ge1 .$$
--
--   This is Eq. (57) of the paper. Together with Section 8.5, which rules out $r=1$ by the continuity axiom, and the simplicity axiom, it yields $K=N^2$, the quantum value.
--
--   **Formalization Note** $K$ is a function `ℕ → ℕ`. Its value at $N=0$ is unconstrained and irrelevant. The paper's standing fact $K\ge1$ is not assumed, because it follows from the two hypotheses.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 16, Section 8.1, Eqs. (56)–(57) (with Appendix 2, pp. 29–30)

import Mathlib

namespace HardyFiveAxioms

/-- Hardy 2001, Section 8.1, Eq. (57): if the number of degrees of freedom `K(N)` satisfies
`K(N+1) ≥ K(N) + 1` (consequence of the subspace axiom) and `K(N_A N_B) = K(N_A) K(N_B)`
(composite systems axiom), then `K(N) = N^r` for a positive integer `r`. -/
theorem dof_eq_pow (K : ℕ → ℕ)
    (hinc : ∀ N : ℕ, 1 ≤ N → K N + 1 ≤ K (N + 1))
    (hmul : ∀ NA NB : ℕ, 1 ≤ NA → 1 ≤ NB → K (NA * NB) = K NA * K NB) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ N : ℕ, 1 ≤ N → K N = N ^ r := by sorry

end HardyFiveAxioms
