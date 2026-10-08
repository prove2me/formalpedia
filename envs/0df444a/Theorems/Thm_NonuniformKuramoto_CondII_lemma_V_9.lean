-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondII_lemma_V_9
-- name    : NonuniformKuramoto.CondII.lemma_V_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:26:01.196846+00:00
-- url     : https://prove2.me/theorems/b82a344d-e612-4880-91f2-c902ba8ed28c
-- title:
--   Lemma V.9 — (Bx)ᵀdiag(A_ij)(Bx) ≥ (λ₂(L(A_ij))/n)‖Bx‖₂² for a connected graph
-- statement:
--   Let $A=A^T\in\mathbb R^{n\times n}$, $n\ge2$, be a nonnegative matrix whose induced graph (edges $\{i,j\}$ with $a_{ij}>0$) is connected, let $B$ be the incidence matrix of that graph and $L(A_{ij})$ its Laplacian. Then for every $x\in\mathbb R^n$,
--   $$
--   (Bx)^T\operatorname{diag}(A_{ij})(Bx)\ \ge\ \frac{\lambda_2(L(A_{ij}))}{n}\,\|Bx\|_2^2 .
--   $$
--   Here $(Bx)^T\operatorname{diag}(A_{ij})(Bx)=\sum_{i<j,\,a_{ij}>0}a_{ij}(x_j-x_i)^2$ and $\|Bx\|_2^2=\sum_{i<j,\,a_{ij}>0}(x_j-x_i)^2$.
--
--   The lemma converts the quadratic form of the Laplacian into a multiple of the squared norm of the edge differences; with $A_{ij}=P_{ij}\cos\varphi_{ij}$ it yields the negative term of the bound (37).
--
--   **Formalization Note** $n\ge2$ is needed for $\lambda_2$ to exist; the platform's `lambda2` is $0$ otherwise.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 25, Lemma V.9

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondII_Constants
open Matrix

namespace NonuniformKuramoto.CondII

/-- Lemma V.9 (Dörfler–Bullo, arXiv:0910.5673v4, p. 25): for a connected graph induced by a
nonnegative symmetric `A`, with incidence matrix `B` and Laplacian `L(A_ij)`, every `x ∈ ℝⁿ`
satisfies `(Bx)ᵀ diag(A_ij) (Bx) ≥ (λ₂(L(A_ij)) / n) ‖Bx‖₂²`. -/
theorem lemma_V_9 {n : ℕ} (A : Fin n → Fin n → ℝ) (hn : 2 ≤ n)
    (hA : ∀ i j, A i j = A j i) (hA0 : ∀ i j, 0 ≤ A i j) (hconn : IsConnectedGraph A)
    (x : Fin n → ℝ) :
    (incB A *ᵥ x) ⬝ᵥ (diagonal (fun e : Edges A => A e.1.1 e.1.2) *ᵥ (incB A *ᵥ x)) ≥
      lambda2 A / n * euclNorm (incB A *ᵥ x) ^ 2 := by sorry

end NonuniformKuramoto.CondII
