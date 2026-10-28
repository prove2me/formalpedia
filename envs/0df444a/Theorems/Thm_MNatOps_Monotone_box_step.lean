-- Prove2me | Theorems.Thm_MNatOps_Monotone_box_step
-- name    : MNatOps.Monotone.box_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:39.232285+00:00
-- url     : https://prove2.me/theorems/dd3568ae-b724-4279-b210-048d917a3ea7
-- title:
--   Proof of Theorem 3, p. 11 — the moves a′ − (eᵢ − eⱼ) and a + (eᵢ − eⱼ) stay in the box
-- statement:
--   Let $B = [l, u] \cap \mathbb Z^n$ be a box with $l_k \in \mathbb Z \cup \{-\infty\}$, $u_k \in \mathbb Z \cup \{+\infty\}$. Let $a, a' \in B$, let $i$ be a coordinate with $a_i < a'_i$, and let $j$ be either $0$ (with $\mathbf e_0 = 0$) or a coordinate with $a'_j < a_j$. Then
--   $$
--   a' - (\mathbf e_i - \mathbf e_j) \in B \quad\text{and}\quad a + (\mathbf e_i - \mathbf e_j) \in B.
--   $$
--
--   This is the box-feasibility step of the proof of Theorem 3: the two exchange moves used there never leave the feasible region.
--
--   **Formalization Note** Over $\mathbb Z$, the paper's "for small $\alpha \in [0, \alpha_0] \cap \mathcal F$" is taken at $\alpha = 1$. The index $j = 0$ is `none`.
-- source:
--   Chen & Li, M♮-Convexity and Its Applications in Operations, SSRN 3431474 (PDF sha256 ea81b5d5…), p. 11, proof of Theorem 3, 'Since B is a box, …'

import Mathlib
import Definitions.Def_MNatOps_Monotone_Model

namespace MNatOps.Monotone

theorem box_step {n : ℕ} (l : Fin n → WithBot ℤ) (u : Fin n → WithTop ℤ) (a a' : Fin n → ℤ)
    (ha : inBox l u a) (ha' : inBox l u a') (i : Fin n) (hi : a i < a' i)
    (j : Option (Fin n)) (hj : ∀ k, j = some k → a' k < a k) :
    inBox l u (a' - dir i j) ∧ inBox l u (a + dir i j) := by sorry

end MNatOps.Monotone
