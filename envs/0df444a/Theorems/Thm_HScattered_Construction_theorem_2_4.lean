-- Prove2me | Theorems.Thm_HScattered_Construction_theorem_2_4
-- name    : HScattered.Construction.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:01.824457+00:00
-- url     : https://prove2.me/theorems/5ffb44ab-524e-452c-98ea-38fa2c926f71
-- title:
--   Theorem 2.4 — the direct sum of h_i-scattered subspaces is min h_i-scattered
-- statement:
--   Let $V_1,\dots,V_t$ be finite-dimensional $\mathbb F_{q^n}$-vector spaces, $V_i=V(r_i,q^n)$, and let $V=V_1\oplus\dots\oplus V_t$, so $V=V(r,q^n)$ with $r=r_1+\dots+r_t$. For each $i$ let $U_i$ be an $h_i$-scattered $\mathbb F_q$-subspace of $V_i$. Then
--
--   $$
--   U=U_1\oplus\dots\oplus U_t \ \text{ is } h\text{-scattered in } V,\qquad h=\min\{h_1,\dots,h_t\}.
--   $$
--
--   This generalises the direct-sum theorem for scattered subspaces ($h=1$) of Bartoli, Giulietti, Marino and Polverino, and is the gluing step of the construction in Theorem 2.6.
--
--   **Formalization Note** $V$ is the external direct sum `(i : Fin t) → V i` and $U$ is `Submodule.pi Set.univ U`. The minimum is expressed by two hypotheses, $h\le h_i$ for all $i$ and $h=h_i$ for some $i$; the latter also forces $t\ge 1$. Each $h_i$-scatteredness includes $0<h_i<r_i$.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 6, Theorem 2.4 (first sentence)

import Mathlib
import Definitions.Def_HScattered_Construction_IsHScattered

namespace HScattered.Construction

/-- Theorem 2.4, first sentence (arXiv:1906.10590v2, p. 6): let `V = V₁ ⊕ … ⊕ V_t` (external
direct sum of `𝔽_{qⁿ}`-spaces) and let `Uᵢ` be an `hᵢ`-scattered `𝔽_q`-subspace of `Vᵢ`.
Then `U = U₁ ⊕ … ⊕ U_t` is h-scattered in `V` with `h = min{h₁, …, h_t}`. -/
theorem theorem_2_4 {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    {t : ℕ} {V : Fin t → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, Module F (V i)] [∀ i, IsScalarTower F K (V i)] [∀ i, FiniteDimensional K (V i)]
    (U : (i : Fin t) → Submodule F (V i)) (hs : Fin t → ℕ)
    (hU : ∀ i, HScattered.Bound.IsHScattered F K (hs i) (U i))
    (h : ℕ) (h_le : ∀ i, h ≤ hs i) (h_eq : ∃ i, hs i = h) :
    HScattered.Bound.IsHScattered F K h (Submodule.pi Set.univ U) := by sorry

end HScattered.Construction
