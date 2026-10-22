-- Prove2me | Theorems.Thm_GeomDL_Blueprint_blueprint_invariant
-- name    : GeomDL.Blueprint.blueprint_invariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:22.378889+00:00
-- url     : https://prove2.me/theorems/af16e09a-d95e-464f-9f0b-3e8dd495f6ac
-- title:
--   §3.5, p. 29 — the Geometric Deep Learning Blueprint f = A ∘ σ_J ∘ B_J ∘ P_{J−1} ∘ … ∘ σ_1 ∘ B_1 is G-invariant
-- statement:
--   Let one group $\mathfrak G$ act on every domain $\Omega_j$ and $\Omega'_j$ ($j \ge 0$), and on signals by $(\mathfrak g . x)(u) = x(\mathfrak g^{-1}u)$. Suppose
--
--   1. every layer $B_j : X(\Omega_j, C_j) \to X(\Omega'_j, D_j)$ is $\mathfrak G$-equivariant;
--   2. every $\sigma_j : D_j \to E_j$ is an arbitrary map, applied element-wise;
--   3. every pooling $P_j : X(\Omega'_j, E_j) \to X(\Omega_{j+1}, C_{j+1})$ is $\mathfrak G$-equivariant;
--   4. the global pooling $A : X(\Omega'_n, E_n) \to Y$ is $\mathfrak G$-invariant.
--
--   Then the blueprint network
--   $$f = A \circ \boldsymbol\sigma_n \circ B_n \circ P_{n-1} \circ \cdots \circ P_0 \circ \boldsymbol\sigma_0 \circ B_0 : X(\Omega_0, C_0) \to Y$$
--   is $\mathfrak G$-invariant, for every number $n + 1 \ge 1$ of layers.
--
--   This is the invariance claim of the book's Geometric Deep Learning Blueprint.
--
--   **Formalization Note** The book's box requires the poolings $P$ only to map to a coarser domain, not to be equivariant; without equivariance of $P$ the composite need not be invariant, so condition 3 is added. The box also allows different blocks to use different groups; this statement uses a single group. Indices run from $0$ to $n = J - 1$ instead of $1$ to $J$.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §3.5, Geometric Deep Learning Blueprint box, p. 29

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

namespace GeomDL.Blueprint

/-- Bronstein et al., §3.5, p. 29 (the Geometric Deep Learning Blueprint, corrected): with one
group `G` acting on every domain, if every layer `B j` and every pooling `P j` is
`G`-equivariant, every `σ j` acts element-wise, and the global pooling `A` is `G`-invariant, then
`f = A ∘ σ_J ∘ B_J ∘ P_{J−1} ∘ … ∘ P_1 ∘ σ_1 ∘ B_1` is `G`-invariant (here `J = n + 1`, indices
from `0`). The printed box does not require the poolings `P` to be equivariant. -/
theorem blueprint_invariant {G : Type*} [Group G] {Ω Ω' : ℕ → Type*} {C D E : ℕ → Type*}
    {Y : Type*} [∀ j, MulAction G (Ω j)] [∀ j, MulAction G (Ω' j)]
    (B : ∀ j, (Ω j → C j) → (Ω' j → D j)) (σ : ∀ j, D j → E j)
    (P : ∀ j, (Ω' j → E j) → (Ω (j + 1) → C (j + 1))) (n : ℕ) (A : (Ω' n → E n) → Y)
    (hB : ∀ j, IsEquivariant (G := G) (B j)) (hP : ∀ j, IsEquivariant (G := G) (P j))
    (hA : IsInvariant (G := G) A) :
    IsInvariant (G := G) (blueprint B σ P n A) := by sorry

end GeomDL.Blueprint
