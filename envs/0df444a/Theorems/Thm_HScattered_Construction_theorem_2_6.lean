-- Prove2me | Theorems.Thm_HScattered_Construction_theorem_2_6
-- name    : HScattered.Construction.theorem_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:03.311714+00:00
-- url     : https://prove2.me/theorems/a7b50f61-d665-479e-97c0-0ac01b7dc294
-- title:
--   Theorem 2.6 — if h + 1 | r and n ≥ h + 1, maximum h-scattered subspaces of dimension rn/(h + 1) exist
-- statement:
--   Let $V=V(r,q^n)$ be an $r$-dimensional vector space over $\mathbb F_{q^n}$, $r\ge1$, and let $h\ge1$. If $h+1$ divides $r$ and $n\ge h+1$, then $V$ contains a maximum $h$-scattered $\mathbb F_q$-subspace $U$ with
--
--   $$
--   \dim_{\mathbb F_q}U=\frac{rn}{h+1}.
--   $$
--
--   Together with bound (1) of Theorem 2.3 this determines the largest dimension of an $h$-scattered subspace of $V(r,q^n)$ whenever $h+1\mid r$ and $n\ge h+1$: it is exactly $rn/(h+1)$.
--
--   **Formalization Note** The dimension equality is stated as $(h+1)\dim_{\mathbb F_q}U=rn$ with $r=\dim_{\mathbb F_{q^n}}V$ and $n=\dim_{\mathbb F_q}\mathbb F_{q^n}$. The hypothesis $r\ge1$ makes explicit that $V(r,q^n)$ is nonzero: $h+1$ divides $0$, but the zero space has no $h$-scattered subspace. $h\ge1$ is the lower end of the range in Definition 1.1; the upper end $h<r$ follows from $h+1\mid r$. Both maximality and the dimension are part of the conclusion.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 7, Theorem 2.6

import Mathlib
import Definitions.Def_HScattered_Construction_IsHScattered

namespace HScattered.Construction

/-- Theorem 2.6 (arXiv:1906.10590v2, p. 7): if `h + 1` divides `r` and `n ≥ h + 1`, then
`V = V(r, qⁿ)` (`r ≥ 1`) contains a maximum h-scattered `𝔽_q`-subspace of dimension
`rn/(h + 1)` (stated as `(h + 1) · dim_{𝔽_q} U = r · n`). -/
theorem theorem_2_6 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (hh : 0 < h) (hr : 0 < Module.finrank K V)
    (hdvd : (h + 1) ∣ Module.finrank K V) (hn : h + 1 ≤ Module.finrank F K) :
    ∃ U : Submodule F V, IsMaximumHScattered F K h U ∧
      (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K := by sorry

end HScattered.Construction
