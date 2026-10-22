-- Prove2me | Theorems.Thm_GeomDL_Sets_isomorphic_graphs_same_output
-- name    : GeomDL.Sets.isomorphic_graphs_same_output
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:15.90808+00:00
-- url     : https://prove2.me/theorems/359a585b-6dae-4424-8428-e3d61644e2f3
-- title:
--   §4.1, p. 35 — permutation invariant and equivariant functions agree on isomorphic graphs
-- statement:
--   Let $(\mathbf X,\mathbf A)$ and $(\mathbf X',\mathbf A')$ be two attributed graphs on the node set $\{1,\dots,n\}$ that are isomorphic through the relabelling $\sigma\in\Sigma_n$ with permutation matrix $\mathbf P$, that is, $\mathbf A'=\mathbf P\mathbf A\mathbf P^\top$ and $\mathbf X'=\mathbf P\mathbf X$. Let $f$ be permutation invariant in the sense of (9) and $\mathbf F$ permutation equivariant in the sense of (10). Then
--
--   $$f(\mathbf X',\mathbf A')=f(\mathbf X,\mathbf A)\qquad\text{and}\qquad \mathbf F(\mathbf X',\mathbf A')_{\sigma(u)}=\mathbf F(\mathbf X,\mathbf A)_u\ \text{ for every node }u.$$
--
--   In words, an invariant function returns the same output on isomorphic graphs, and an equivariant function returns the same output at corresponding nodes.
--
--   **Formalization Note** "Isomorphic (topologically-equivalent)" is made explicit as the existence of the relabelling $\sigma$ carrying adjacency and features of one graph to those of the other.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.1, p. 35

import Mathlib
import Definitions.Def_GeomDL_Sets_Defs

namespace GeomDL.Sets

/-- §4.1, p. 35: permutation invariant and equivariant functions produce identical outputs on
isomorphic graphs. Two attributed graphs `(X, A)` and `(X', A')` on the node set `{1,…,n}` are
isomorphic via the relabelling `σ ∈ Σₙ` when `A' = PAPᵀ` and `X' = PX`. Then an invariant `f`
(eq. (9)) has `f(X', A') = f(X, A)`, and an equivariant `F` (eq. (10)) gives node `σ(u)` of the
second graph the output of node `u` of the first. -/
theorem isomorphic_graphs_same_output {n d d' : ℕ} {Y : Type*}
    (f : Matrix (Fin n) (Fin d) ℝ → Matrix (Fin n) (Fin n) ℝ → Y)
    (F : Matrix (Fin n) (Fin d) ℝ → Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin d') ℝ)
    (hf : IsGraphPermInvariant f) (hF : IsGraphPermEquivariant F)
    (σ : Equiv.Perm (Fin n)) (X X' : Matrix (Fin n) (Fin d) ℝ) (A A' : Matrix (Fin n) (Fin n) ℝ)
    (hA : A' = permAdj σ A) (hX : X' = permRows σ X) :
    f X' A' = f X A ∧ ∀ u : Fin n, F X' A' (σ u) = F X A u := by sorry

end GeomDL.Sets
