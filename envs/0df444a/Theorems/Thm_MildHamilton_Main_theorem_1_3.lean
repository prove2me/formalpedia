-- Prove2me | Theorems.Thm_MildHamilton_Main_theorem_1_3
-- name    : MildHamilton.Main.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:46:33.2122+00:00
-- url     : https://prove2.me/theorems/697929f0-d04b-4b58-9bfb-7af2d4a3dff9
-- title:
--   Theorem 1.3, p. 2 — mildly pseudorandom regular graphs are Hamiltonian
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be an $(n,d,\lambda)$-graph and let $\delta\in(0,1)$. If
--
--   $$\lambda\le(1-\delta)d\qquad\text{and}\qquad d\ge C\,\delta^{-6}(\log n)^3,$$
--
--   then $G$ is Hamiltonian.
--
--   This is the main theorem of the paper. It reaches any fixed spectral gap, however small, at polylogarithmic degree, and the dependence on $\delta$ is explicit.
--
--   **Formalization Note** The logarithm is natural. The constant $C$ is chosen before the graph. Hamiltonicity is Mathlib's `SimpleGraph.IsHamiltonian`, under which the one-vertex graph is Hamiltonian.
--
--   Differences from the source:
--   - encoding: all non-trivial eigenvalues of the adjacency matrix have absolute value at most λ → the published ExplicitExpanders.Attach.IsNDLambda: every eigenvalue with an eigenvector orthogonal to the all-ones vector; reason: for a d-regular graph the all-ones vector spans an eigenline for the top eigenvalue, so the eigenvalues on its orthogonal complement are the spectrum with one copy of d removed; multiplicity counts, and a disconnected graph keeps a second copy of d
--   - encoding: an n-vertex graph → a finite nonempty vertex type; reason: Mathlib declares the empty graph non-Hamiltonian; n = 1 holds by its convention, and the paper does not discuss n = 0
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Theorem 1.3, p. 2

import Mathlib
import Definitions.Def_ExplicitExpanders_Attach_IsNDLambda

namespace MildHamilton.Main

/-- Theorem 1.3 (Muyesser, STOC 2027 submission #233, p. 2): every `(n, d, λ)`-graph with `λ ≤ (1 − δ) d` and
`d ≥ C δ⁻⁶ (log n)³`, for `δ ∈ (0, 1)` and an absolute constant `C`, is Hamiltonian. -/
theorem theorem_1_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
        [DecidableRel G.Adj] (n d : ℕ) (lam δ : ℝ),
        ExplicitExpanders.Attach.IsNDLambda G n d lam → 0 < δ → δ < 1 → lam ≤ (1 - δ) * d →
        C * δ ^ (-6 : ℤ) * Real.log n ^ 3 ≤ d → G.IsHamiltonian := by sorry

end MildHamilton.Main
