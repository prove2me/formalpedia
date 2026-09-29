-- Prove2me | Theorems.Thm_Hirsch_face_connected
-- name    : Hirsch.face_connected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T05:15:39.273347+00:00
-- url     : https://prove2.me/theorems/85dac696-c994-4fe2-9f76-b5507f872a18
-- title:
--   Two vertices are joined inside the face they share
-- statement:
--   **Vertices are connected within their common face.** Let $P = \{x \in \mathbb{R}^d : \langle a_i, x\rangle \le b_i,\ i < n\}$ be a bounded H-polytope and let $u, v$ be two vertices of $P$. Then there is a walk from $u$ to $v$ in the vertex-edge graph of $P$ along which **every** inequality that is tight at both $u$ and $v$ stays tight:
--
--   $$\langle a_i, u\rangle = b_i \ \text{ and } \ \langle a_i, v\rangle = b_i \;\Longrightarrow\; \langle a_i, w_k\rangle = b_i \quad \text{for every } k.$$
--
--   Equivalently, $u$ and $v$ can be joined without leaving the smallest face of $P$ that contains them both; in particular the graph of every face of $P$ is connected, and taking the face to be $P$ itself recovers Balinski's connectivity of the graph of a polytope.
--
--   This is the structural property of polytope graphs on which the classical diameter bounds rest. Eisenbrand, Hähnle, Razborov and Rothvoß isolated it as *the* hypothesis of a purely combinatorial abstraction — a graph whose vertices are $d$-subsets of an $n$-set in which any two vertices $u, v$ are joined by a path through vertices containing $u \cap v$ — and showed that both Larman's bound $n 2^{d-3}$ and the Kalai–Kleitman bound $n^{\log_2 d + 2}$ already follow from it. It is also what makes the facet induction in those proofs work: distances measured inside a facet bound distances in the polytope.
--
--   The walk is allowed to repeat a point (a step is either stationary or along an edge), matching the convention of `DiamLE`; no bound on its length is asserted here.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961) 431-434; the form used here is the hypothesis of Theorem 2.7 in Kim and Santos, An update on the Hirsch conjecture, arXiv:0907.1186, which is due to Eisenbrand, Haehnle, Razborov and Rothvoss, Diameter of polyhedra: limits of abstraction, Math. Oper. Res. 35 (2010) 786-794.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem face_connected (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b)) :
    ∃ (L : ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)), w 0 = u ∧ w L = v ∧
      (∀ k < L, w k = w (k + 1) ∨ Adj (Hpoly a b) (w k) (w (k + 1))) ∧
      (∀ k ≤ L, ∀ i : Fin n, ⟪a i, u⟫ = b i → ⟪a i, v⟫ = b i → ⟪a i, w k⟫ = b i) := by sorry

end Hirsch
