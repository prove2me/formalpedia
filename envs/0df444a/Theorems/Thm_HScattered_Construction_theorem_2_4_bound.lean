-- Prove2me | Theorems.Thm_HScattered_Construction_theorem_2_4_bound
-- name    : HScattered.Construction.theorem_2_4_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:05.010184+00:00
-- url     : https://prove2.me/theorems/12a792dd-aef9-438d-8452-601cad14a705
-- title:
--   Theorem 2.4 (second part) — direct sums of subspaces reaching bound (1) reach bound (1)
-- statement:
--   Let $t\ge1$, let $V_1,\dots,V_t$ be finite-dimensional $\mathbb F_{q^n}$-vector spaces with $V_i=V(r_i,q^n)$, and let $V=V_1\oplus\dots\oplus V_t=V(r,q^n)$. Suppose each $U_i$ is an $h$-scattered $\mathbb F_q$-subspace of $V_i$ (the same $h$ for all $i$) whose dimension reaches bound (1), $\dim_{\mathbb F_q}U_i=r_in/(h+1)$. Then $U=U_1\oplus\dots\oplus U_t$ is $h$-scattered in $V$ and
--
--   $$
--   \dim_{\mathbb F_q} U=\frac{rn}{h+1}.
--   $$
--
--   Since bound (1) holds for every $h$-scattered subspace that does not define a subgeometry, this produces subspaces of the largest possible dimension in $V$ from such subspaces in the summands.
--
--   **Formalization Note** Both dimension equalities are stated multiplied out: $(h+1)\dim_{\mathbb F_q}U_i=r_in$ and $(h+1)\dim_{\mathbb F_q}U=rn$, where $n=\dim_{\mathbb F_q}\mathbb F_{q^n}$ and $r=\dim_{\mathbb F_{q^n}}V$. The hypothesis $t\ge1$ is added because for $t=0$ the space $V$ is zero and has no $h$-scattered subspace.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 6, Theorem 2.4 (second sentence)

import Mathlib
import Definitions.Def_HScattered_Construction_IsHScattered

namespace HScattered.Construction

/-- Theorem 2.4, second sentence (arXiv:1906.10590v2, p. 6): let `V = V₁ ⊕ … ⊕ V_t`, `t ≥ 1`,
`Vᵢ = V(rᵢ, qⁿ)`, `V = V(r, qⁿ)`. If every `Uᵢ` is h-scattered in `Vᵢ` and reaches bound (1),
`dim_{𝔽_q} Uᵢ = rᵢ n/(h + 1)`, then `U = U₁ ⊕ … ⊕ U_t` is h-scattered in `V` and
`dim_{𝔽_q} U = rn/(h + 1)`. Divisions are stated as multiplications. -/
theorem theorem_2_4_bound {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    {t : ℕ} (ht : 0 < t) {V : Fin t → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, Module F (V i)] [∀ i, IsScalarTower F K (V i)] [∀ i, FiniteDimensional K (V i)]
    (h : ℕ) (U : (i : Fin t) → Submodule F (V i))
    (hU : ∀ i, HScattered.Bound.IsHScattered F K h (U i))
    (hdim : ∀ i, (h + 1) * Module.finrank F (U i) =
      Module.finrank K (V i) * Module.finrank F K) :
    HScattered.Bound.IsHScattered F K h (Submodule.pi Set.univ U) ∧
      (h + 1) * Module.finrank F (Submodule.pi Set.univ U) =
        Module.finrank K ((i : Fin t) → V i) * Module.finrank F K := by sorry

end HScattered.Construction
