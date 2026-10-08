-- Prove2me | Theorems.Thm_KleinbergHITS_Conv_io_matrix_form
-- name    : KleinbergHITS.Conv.io_matrix_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:58.016739+00:00
-- url     : https://prove2.me/theorems/61f46c0f-2022-4b6a-9dc8-4c1668b0e53f
-- title:
--   §3, proof of Theorem 3.1, p. 10 — the I and O operations are x ← Aᵀy and y ← Ax
-- statement:
--   Let $G=(V,E)$ be a directed graph on the pages $p_1,\dots,p_n$ and let $A$ be its adjacency matrix, $A_{ij}=1$ if $(p_i,p_j)\in E$ and $0$ otherwise. The $\mathcal I$ operation sends hub weights $y$ to the authority weights $\mathcal I(y)_p=\sum_{q:(q,p)\in E}y_q$, and the $\mathcal O$ operation sends authority weights $x$ to the hub weights $\mathcal O(x)_p=\sum_{q:(p,q)\in E}x_q$. Then, for all vectors $x,y\in\mathbb R^n$,
--   $$\mathcal I(y)=A^{\top}y,\qquad \mathcal O(x)=Ax.$$
--
--   This is the step that turns the combinatorial update rules of the algorithm into linear algebra: after it, the iterates are products of the matrices $A^{\top}A$ and $AA^{\top}$ applied to the all-ones vector.
--
--   **Formalization Note** No assumption on $G$ is needed; in particular Assumption (†) is not used.
-- source:
--   Kleinberg, Authoritative sources in a hyperlinked environment, J. ACM 46(5) (1999), author's copy, p. 10, §3, proof of Theorem 3.1 ("One easily verifies that the I and O operations can be written x ← Aᵀy and y ← Ax respectively")

import Mathlib
import Definitions.Def_KleinbergHITS_Conv_Setting

namespace KleinbergHITS.Conv

open Matrix

/-- Kleinberg (1999), §3, proof of Theorem 3.1, p. 10: "One easily verifies that the I and O
operations can be written x ← Aᵀy and y ← Ax respectively." -/
theorem io_matrix_form {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] :
    (∀ y : Fin n → ℝ, opI E y = (adjMatrix E)ᵀ *ᵥ y) ∧
      (∀ x : Fin n → ℝ, opO E x = adjMatrix E *ᵥ x) := by sorry

end KleinbergHITS.Conv
