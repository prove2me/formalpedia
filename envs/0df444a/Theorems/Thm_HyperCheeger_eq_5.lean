-- Prove2me | Theorems.Thm_HyperCheeger_eq_5
-- name    : HyperCheeger.eq_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:03:12.207205+00:00
-- url     : https://prove2.me/theorems/bf923484-a042-47e4-aa5c-94ed2df4e578
-- title:
--   Eq. (5) — the quadratic form of $L_H$
-- statement:
--   Let $H$ be a hypergraph and $x\in\mathbb R^{V_H}$. The quadratic form of the Laplacian $L_H$ is
--
--   $$x^{T}L_Hx=\sum_{e\in E_H}\frac{w_H(e)}{|e|-1}\sum_{\{u,v\}\subseteq e}(x(u)-x(v))^2.$$
--
--   In particular $L_H$ is positive semidefinite, with the quadratic form measuring how different the values of $x$ are across vertices in the same hyperedge.
--
--   Differences from the source:
--   - encoding: a sum over unordered pairs {u,v} ⊆ e → 1/2 of the sum over ordered pairs (u,v) ∈ e × e; reason: terms with u = v vanish and each unordered pair appears twice
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), eq. (5), p.7

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_nu2

open scoped Matrix

namespace HyperCheeger

/-- **Eq. (5)**: the quadratic form of the Laplacian,
`xᵀ L_H x = ∑_{e ∈ E} (w_H(e)/(|e|−1)) ∑_{{u,v} ⊆ e} (x(u) − x(v))²`.

Kamal, Bagchi, *A Cheeger Inequality for Hypergraphs and Its Applications*, STOC 2027 submission,
arXiv:2609.16286 (manuscript sha256 e0942b89…), eq. (5), p.7.

**Formalization Note.** The sum over unordered pairs is written as `1/2` of the sum over ordered
pairs `(u, v) ∈ e × e`; the terms with `u = v` vanish. -/
theorem eq_5 {V : Type} [Fintype V] [DecidableEq V] (H : Hypergraph V) (x : V → ℝ) :
    x ⬝ᵥ (H.lap *ᵥ x) =
      ∑ e ∈ H.edges, H.w e / ((e.card : ℝ) - 1) * (1 / 2 * ∑ u ∈ e, ∑ v ∈ e, (x u - x v) ^ 2) := by sorry

end HyperCheeger
