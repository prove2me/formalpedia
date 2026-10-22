-- Prove2me | Theorems.Thm_GeomDL_EGNN_eq_35_perm_equivariant
-- name    : GeomDL.EGNN.eq_35_perm_equivariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T18:14:20.885528+00:00
-- url     : https://prove2.me/theorems/dcc4c62a-5dfb-4607-ac15-92b9b7dc8f17
-- title:
--   §5.3, eq. (35), pp. 78–79 — the message-passing GNN layer is permutation equivariant
-- statement:
--   Let $\mathbf A\in\mathbb R^{n\times n}$ be an adjacency matrix with neighbourhoods $\mathcal N_u$, let $\mathbf X$ assign a feature $\mathbf x_u$ to each node $u$, and let $F$ be the message-passing layer (35),
--   $$F(\mathbf X,\mathbf A)_u = \phi\Big(\mathbf x_u, \bigoplus_{v\in\mathcal N_u}\psi(\mathbf x_u,\mathbf x_v)\Big),$$
--   for arbitrary functions $\phi$, $\psi$ and an arbitrary aggregator $\bigoplus$ of the multiset of messages. Then for every permutation $\sigma$ of the nodes, with permutation matrix $\mathbf P$,
--   $$F(\mathbf{PX},\mathbf{PAP}^\top) = \mathbf P\,F(\mathbf X,\mathbf A).$$
--
--   This is the equivariance property (10) of §4.1 for the message-passing flavour, the property the book requires of every GNN layer it studies.
--
--   **Formalization Note** Row $u$ of $\mathbf{PX}$ is row $\sigma^{-1}(u)$ of $\mathbf X$, and $(\mathbf{PAP}^\top)_{uv} = a_{\sigma^{-1}(u)\sigma^{-1}(v)}$. The aggregator is any function of a multiset, which is how the book's "permutation-invariant function $\bigoplus$" is encoded.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §5.3, p. 78 ("permutation equivariant functions F(X, A) constructed by applying shared permutation invariant functions") and eq. (35), p. 79; property (10), §4.1, p. 33

import Mathlib
import Definitions.Def_GeomDL_EGNN_Defs

namespace GeomDL.EGNN

/-- §5.3, pp. 78–79: the message-passing layer (35), `h_u = φ(x_u, ⊕_{v ∈ N_u} ψ(x_u, x_v))`,
is permutation equivariant in the sense of (10): `F(PX, PAPᵀ) = P F(X, A)` for every
permutation `σ` (convention: row `u` of `PX` is row `σ⁻¹(u)` of `X`). -/
theorem eq_35_perm_equivariant {n : ℕ} {α M M' β : Type*} (φ : α → M' → β)
    (agg : Multiset M → M') (ψ : α → α → M) (σ : Equiv.Perm (Fin n)) (X : Fin n → α)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    mpLayer φ agg ψ (permRows σ X) (GeomDL.Sets.permAdj σ A) = permRows σ (mpLayer φ agg ψ X A) := by sorry

end GeomDL.EGNN
