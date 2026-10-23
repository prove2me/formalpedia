-- Prove2me | Theorems.Thm_LysgaardLetchfordEglese2004_proposition_1_faithful
-- name    : LysgaardLetchfordEglese2004.proposition_1_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T00:29:26.881545+00:00
-- url     : https://prove2.me/theorems/d4c37f93-9fdf-48d6-b497-780b832e7682
-- title:
--   Proposition 1 (safe shrinking), for LP solution vectors as in the paper
-- statement:
--   Consider the capacitated vehicle routing problem on the complete graph with vertex set $\{0,\dots,n\}$, depot $0$, vehicle capacity $Q>0$ and customers $i=1,\dots,n$ with integer demands $0<q_i\le Q$. For a vertex set $T$, $\delta(T)$ is the set of edges with exactly one end in $T$, $x(\delta(T))$ its total weight, and $r(T)$ the bin-packing number of the customers in $T$ (bins of capacity $Q$). The capacity inequalities are $x(\delta(T))\ge 2r(T)$ for customer sets $T$ with $|T|\ge 2$. Let $x^*$ be a solution of the initial LP relaxation:
--
--   $$x^*(\delta(\{i\}))=2\ (i\ne 0),\qquad 0\le x^*_{ij}\le 1\ (i\ne j \text{ customers}),\qquad 0\le x^*_{0j}\le 2.$$
--
--   Let $S$ be a customer set with $x^*(\delta(S))\le 2$ and $x^*(\delta(R))\ge 2$ for every nonempty proper subset $R$ of $S$. Then for every customer set $T$ with $|T|\ge 2$ and $x^*(\delta(T))<2r(T)$ there is a customer set $T'$ with $|T'|\ge 2$ and $S\subseteq T'$ or $S\cap T'=\emptyset$, such that
--
--   $$2r(T)-x^*(\delta(T))\le 2r(T')-x^*(\delta(T')).$$
--
--   This is Proposition 1 of Lysgaard, Letchford and Eglese (2004) as stated in the paper: shrinking $S$ to a single supervertex is safe for the separation of capacity inequalities. The mission's existing formalization of Proposition 1 proves the same conclusion for every nonnegative edge vector, without the degree equations or upper bounds, so this statement is its specialization to LP solutions.
--
--   **Formalization Note** Customer sets are finite sets of vertices not containing the depot; $Q$ is real. The paper's "$\forall R\subset S$" is read over nonempty proper subsets, since $x(\delta(\emptyset))=0<2$.
-- source:
--   Lysgaard, Letchford & Eglese, A new branch-and-cut algorithm for the capacitated vehicle routing problem, Math. Program. Ser. A 100 (2004) 423-445, doi:10.1007/s10107-003-0481-8, p. 426, Proposition 1 (LP relaxation p. 425; formulation (1), (3), (4) p. 424)

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_binPackingNumber
import Definitions.Def_LysgaardCVRP_Shrink_SafeToShrink

open LysgaardCVRP.Shrink

theorem LysgaardLetchfordEglese2004.proposition_1_faithful {n : ℕ} (q : Fin (n + 1) → ℕ) (Q : ℝ) (hQ : 0 < Q)
    (hq : ∀ i : Fin (n + 1), i ≠ 0 → 0 < q i ∧ (q i : ℝ) ≤ Q)
    (x : Sym2 (Fin (n + 1)) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hdeg : ∀ i : Fin (n + 1), i ≠ 0 → cut x {i} = 2)
    (hub : ∀ i j : Fin (n + 1), i ≠ 0 → j ≠ 0 → i ≠ j → x s(i, j) ≤ 1)
    (hub0 : ∀ j : Fin (n + 1), j ≠ 0 → x s(0, j) ≤ 2)
    (S : Finset (Fin (n + 1))) (hS0 : (0 : Fin (n + 1)) ∉ S) (hS : cut x S ≤ 2)
    (hR : ∀ R : Finset (Fin (n + 1)), R ⊆ S → R.Nonempty → R ≠ S → 2 ≤ cut x R) :
    SafeToShrink x (binPackingNumber q Q) S := by sorry
