-- Prove2me | Theorems.Thm_GeomDL_EGNN_layer_is_message_passing
-- name    : GeomDL.EGNN.layer_is_message_passing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T18:14:08.64617+00:00
-- url     : https://prove2.me/theorems/2d25a008-1be3-4a1e-bf35-e67e57940331
-- title:
--   §5.5, p. 84 — the E(3)-equivariant layer is an instance of the message-passing flavour (35)
-- statement:
--   Consider the Satorras et al. layer $(\mathbf f,\mathbf x)\mapsto(\mathbf f',\mathbf x')$ of p. 84 on a graph with adjacency matrix $\mathbf A$, and regard the pair $(\mathbf f_u,\mathbf x_u)$ as the state of node $u$. Then both halves of the layer are message-passing layers (35):
--   1. the feature update $\mathbf f'$ is (35) on the graph $\mathbf A$, with the same aggregator $\bigoplus$, update $((\mathbf f_u,\mathbf x_u), \mathbf m)\mapsto\phi(\mathbf f_u,\mathbf m)$ and messages $\psi_{\mathrm f}(\mathbf f_u,\mathbf f_v,\|\mathbf x_u-\mathbf x_v\|^2)$;
--   2. the coordinate update $\mathbf x'$ is (35) on the complete graph without self-loops (so $\mathcal N_u = \{v : v \neq u\}$), with the sum as aggregator, update $((\mathbf f_u,\mathbf x_u),\mathbf m)\mapsto \mathbf x_u+\mathbf m$ and messages $(\mathbf x_u-\mathbf x_v)\psi_{\mathrm c}(\mathbf f_u,\mathbf f_v,\|\mathbf x_u-\mathbf x_v\|^2)$:
--   $$\mathbf x'_u = \mathbf x_u + \sum_{v\neq u}(\mathbf x_u-\mathbf x_v)\,\psi_{\mathrm c}(\mathbf f_u,\mathbf f_v,\|\mathbf x_u-\mathbf x_v\|^2).$$
--
--   This is the book's remark that "the computations of such a layer can be seen as a particular instance of the message-passing GNN flavour".
--
--   **Formalization Note** The book does not say over which graph the coordinate update is message passing; because the printed sum runs over all $v\neq u$ rather than $\mathcal N_u$, the statement uses the complete graph for that half and the given graph for the feature half.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §5.5, p. 84, "a particular instance of the “message-passing” GNN flavour"; eq. (35), p. 79

import Mathlib
import Definitions.Def_GeomDL_EGNN_Defs

namespace GeomDL.EGNN

/-- §5.5, p. 84: the equivariant layer is an instance of the message-passing flavour (35), with
node state `(f_u, x_u)`. The feature update is (35) on the graph `A` with update
`(f_u, x_u), m ↦ φ(f_u, m)` and message `ψ_f(f_u, f_v, ‖x_u − x_v‖²)`; the coordinate update is
(35) on the complete graph without self-loops (`N_u = {v ≠ u}`), with the sum as aggregator,
update `(f_u, x_u), m ↦ x_u + m` and message `(x_u − x_v) ψ_c(f_u, f_v, ‖x_u − x_v‖²)`. -/
theorem layer_is_message_passing {n d : ℕ} {M M' F' : Type*} (φ : (Fin d → ℝ) → M' → F')
    (agg : Multiset M → M') (ψf : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → M)
    (ψc : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (f : Matrix (Fin n) (Fin d) ℝ) (x : Fin n → E3) :
    (egnnLayer φ agg ψf ψc A f x).1 =
        mpLayer (fun p m => φ p.1 m) agg
          (fun p q => ψf p.1 q.1 (‖p.2 - q.2‖ ^ 2)) (fun u => (f u, x u)) A ∧
    (egnnLayer φ agg ψf ψc A f x).2 =
        mpLayer (fun p m => p.2 + m) Multiset.sum
          (fun p q => ψc p.1 q.1 (‖p.2 - q.2‖ ^ 2) • (p.2 - q.2)) (fun u => (f u, x u))
          (completeAdj n) := by sorry

end GeomDL.EGNN
