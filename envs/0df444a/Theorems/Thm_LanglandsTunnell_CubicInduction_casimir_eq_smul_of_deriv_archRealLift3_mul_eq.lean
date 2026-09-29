-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_deriv_archRealLift3_mul_eq
-- name    : LanglandsTunnell.CubicInduction.casimir_eq_smul_of_deriv_archRealLift3_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/05c73186-a384-528e-9aee-f3a07005bfde
-- title:
--   Casimir eigenvalues from left diagonal first-order data on GL₃
-- statement:
--   Let $H : \mathrm{Fin}\,3 \to \mathbb{C}$ be a triple of complex scalars and let $\varphi$ be a complex-valued function on $\mathrm{GL}_3$ of the adele ring of $\mathbb{Q}$. Write $\ell(e)$ for [`WhittakerBlock.archRealLift3 e`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L18), the adelic matrix obtained by placing a real $3\times 3$ matrix $e$ at the archimedean place (and $1$ when the result is not invertible). Assume: (i) `IsArchSmooth3 φ`, i.e. for every $g$ the function $e \mapsto \varphi(g\,\ell(e))$ on real $3\times 3$ matrices is $C^\infty$ on the locus $\det e \neq 0$; (ii) for all $i<j$ and all $g$, $\frac{d}{ds}\big|_{0}\varphi(\ell(1+sE_{ij})\,g)=0$; (iii) for each $c$ and all $g$, $\frac{d}{ds}\big|_{0}\varphi(\ell(1+sE_{cc})\,g)=H_c\,\varphi(g)$. Then, with $D_{ij}\varphi(g):=\frac{d}{ds}\big|_{0}\varphi(g\,\ell(1+sE_{ij}))$ the right derivatives and $C_1\varphi=\sum_i D_{ii}\varphi$, $C_2\varphi=\sum_{i,j}D_{ij}D_{ji}\varphi$, $C_3\varphi=\sum_{i,j,k}D_{ij}D_{jk}D_{ki}\varphi$, one has the three identities of functions $C_1\varphi=(H_0+H_1+H_2)\cdot\varphi$, $C_2\varphi=(H_0^2+H_1^2+H_2^2-2H_0+2H_2)\cdot\varphi$ and $C_3\varphi=(H_0^3+H_1^3+H_2^3-2H_0^2+H_1^2+4H_2^2-(H_0H_1+H_0H_2+H_1H_2)-2H_0-2H_1+4H_2)\cdot\varphi$.
--
--   This computes the infinitesimal character of $\varphi$ at the infinite place: first-order left data along the upper elementary matrices (vanishing) and along the diagonal ones (eigenvalues $H_0,H_1,H_2$) determine the action of the three central elements of degrees $1,2,3$ in $U(\mathfrak{gl}_3)$, acting by right derivatives, as multiplication by the diagonal polynomials of `gl3_casimir_normalForm` evaluated at $H$. It is used by `casimir_eq_smul_of_upperTriangular_equivariant`, where the left data come from equivariance under the upper triangular subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_deriv_archRealLift3_mul_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.casimir_eq_smul_of_deriv_archRealLift3_mul_eq
    (H : Fin 3 → ℂ) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hN : ∀ i j : Fin 3, i < j → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * g)) 0 = 0)
    (hH : ∀ (c : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = c then s else 0) * g)) 0 = H c * φ g) :
    WhittakerBlock.casimir1 φ = (H 0 + H 1 + H 2) • φ ∧
    WhittakerBlock.casimir2 φ = (H 0 ^ 2 + H 1 ^ 2 + H 2 ^ 2 - 2 * H 0 + 2 * H 2) • φ ∧
    WhittakerBlock.casimir3 φ =
      (H 0 ^ 3 + H 1 ^ 3 + H 2 ^ 3 - 2 * H 0 ^ 2 + H 1 ^ 2 + 4 * H 2 ^ 2
        - (H 0 * H 1 + H 0 * H 2 + H 1 * H 2) - 2 * H 0 - 2 * H 1 + 4 * H 2) • φ := by sorry
