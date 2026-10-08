-- Prove2me | Theorems.Thm_HScattered_Delsarte_theorem_2_7
-- name    : HScattered.Delsarte.theorem_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:42.352685+00:00
-- url     : https://prove2.me/theorems/129a5a39-61db-47a6-a327-b3d558b04ca0
-- title:
--   Theorem 2.7 — hyperplane intersections of a maximum h-scattered subspace of dimension rn/(h + 1)
-- statement:
--   Let $V$ be an $r$-dimensional $\mathbb F_{q^n}$-vector space and let $U$ be a maximum $h$-scattered $\mathbb F_q$-subspace of $V$ of dimension $rn/(h+1)$. Then every $(r-1)$-dimensional $\mathbb F_{q^n}$-subspace $H$ of $V$ satisfies
--
--   $$
--   \frac{rn}{h+1}-n\ \le\ \dim_{\mathbb F_q}(U\cap H)\ \le\ \frac{rn}{h+1}-n+h .
--   $$
--
--   The upper bound is what makes the Delsarte dual well defined in Theorem 3.3: since $h<n-2$ when $n\ge h+3$, it gives condition ($\diamond$) of Proposition 3.1, and it is the bound contradicted at the end of the proof of Theorem 3.3.
--
--   **Formalization Note** "Of dimension $rn/(h+1)$" is $(h+1)\dim_{\mathbb F_q}U=rn$. Both bounds are written with $n$ moved to the other side, $\dim U\le\dim(U\cap H)+n\le\dim U+h$, so no natural-number subtraction or division occurs. The paper calls the hyperplane $W$; it is `H` here because $W$ is used in §3 for another object. This duplicates the goal of the companion mission on hyperplane intersections.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 8, Theorem 2.7 (restated p. 18)

import Mathlib
import Definitions.Def_HScattered_Delsarte_IsHScattered

namespace HScattered.Delsarte

/-- Theorem 2.7 (arXiv:1906.10590v2, p. 8): if `U` is a maximum h-scattered `𝔽_q`-subspace of
`V = V(r, qⁿ)` of dimension `rn/(h + 1)`, then every hyperplane `H` of `V` satisfies
`rn/(h + 1) − n ≤ dim_{𝔽_q}(U ∩ H) ≤ rn/(h + 1) − n + h`.
The dimension hypothesis is `(h + 1) · dim U = r · n`, and both bounds are written with `n`
moved to the other side, so no natural-number subtraction or division occurs. -/
theorem theorem_2_7 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsMaximumHScattered F K h U)
    (hdim : (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K)
    (H : Submodule K V) (hH : Module.finrank K H + 1 = Module.finrank K V) :
    Module.finrank F U ≤ Module.finrank F ↥(H.restrictScalars F ⊓ U) + Module.finrank F K ∧
      Module.finrank F ↥(H.restrictScalars F ⊓ U) + Module.finrank F K ≤
        Module.finrank F U + h := by sorry

end HScattered.Delsarte
