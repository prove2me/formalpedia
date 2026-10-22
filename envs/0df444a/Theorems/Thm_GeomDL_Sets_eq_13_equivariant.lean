-- Prove2me | Theorems.Thm_GeomDL_Sets_eq_13_equivariant
-- name    : GeomDL.Sets.eq_13_equivariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:16.946472+00:00
-- url     : https://prove2.me/theorems/ddde4c5f-e438-4853-8fdd-c6c9a611872a
-- title:
--   §4.1, eq. (13), p. 34 — the local construction F(X, A)ᵤ = φ(xᵤ, X_{Nᵤ}) satisfies (10)
-- statement:
--   Let $\mathbf A\in\mathbb R^{n\times n}$ be an adjacency matrix and $\mathbf X\in\mathbb R^{n\times d}$ node features. For a node $u$ let $\mathcal N_u=\{v:a_{uv}\ne0\text{ or }a_{vu}\ne0\}$ be its neighbourhood (11) and $\mathbf X_{\mathcal N_u}=\{\!\{\mathbf x_v:v\in\mathcal N_u\}\!\}$ the multiset of its neighbours' features (12). Let $\phi:\mathbb R^d\times\{\text{finite multisets of }\mathbb R^d\}\to\mathbb R^{d'}$ be any function, and let $\mathbf F(\mathbf X,\mathbf A)$ be the matrix whose $u$-th row is $\phi(\mathbf x_u,\mathbf X_{\mathcal N_u})$, eq. (13). Then $\mathbf F$ is permutation equivariant in the sense of (10):
--
--   $$\mathbf F(\mathbf P\mathbf X,\mathbf P\mathbf A\mathbf P^\top)=\mathbf P\,\mathbf F(\mathbf X,\mathbf A)\quad\text{for every permutation matrix }\mathbf P.$$
--
--   This is the book's general recipe for permutation-equivariant functions on graphs: a shared local function that is invariant to the order of the neighbours.
--
--   **Formalization Note** Since $\phi$ receives a multiset, its output does not depend on the ordering of the nodes in $\mathcal N_u$ — the book's hypothesis "$\phi$ is permutation invariant" holds by construction. Edges are the nonzero entries of $\mathbf A$, which for the 0/1 matrix (8) is the book's edge set.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.1, eqs. (11)–(13), p. 34

import Mathlib
import Definitions.Def_GeomDL_Sets_Defs

namespace GeomDL.Sets

/-- §4.1, eq. (13), p. 34: the local construction `F(X, A)_u = φ(x_u, X_{N_u})` with a shared
`φ` that receives the neighbourhood features as a multiset (hence is permutation invariant in
them) satisfies (10): `F(PX, PAPᵀ) = P F(X, A)` for every permutation matrix `P`. -/
theorem eq_13_equivariant {n d d' : ℕ}
    (φ : (Fin d → ℝ) → Multiset (Fin d → ℝ) → (Fin d' → ℝ)) :
    IsGraphPermEquivariant (localLayer φ : Matrix (Fin n) (Fin d) ℝ → Matrix (Fin n) (Fin n) ℝ →
      Matrix (Fin n) (Fin d') ℝ) := by sorry

end GeomDL.Sets
