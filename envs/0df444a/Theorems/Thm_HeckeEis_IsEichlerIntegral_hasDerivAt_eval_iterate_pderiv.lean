-- Prove2me | Theorems.Thm_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv
-- name    : HeckeEis.IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/4c48bd9d-6fab-56fd-ba21-25237f94d44e
-- title:
--   Bol's identity one rung at a time
-- statement:
--   Fix $n \in \mathbb{N}$, a function $g \colon \mathfrak{H} \to \mathbb{C}$ on the upper half-plane, and a map $G$ from $\mathfrak{H}$ to the submodule $\mathrm{BinaryForm}\ \mathbb{C}\ n$ of $\mathbb{C}$-polynomials in the two variables $X_0, X_1$ that are homogeneous of degree $n$. Assume $\mathrm{IsEichlerIntegral}\ n\ g\ G$, i.e. for every exponent vector $d \colon \mathrm{Fin}\ 2 \to_0 \mathbb{N}$ and every $\tau \in \mathfrak{H}$ the function $z \mapsto \operatorname{coeff}_d\bigl(G(\mathrm{ofComplex}\ z)\bigr)$ of a complex variable has derivative $g(\tau)\cdot\operatorname{coeff}_d\bigl((\tau X_0 + X_1)^n\bigr)$ at the point $\tau$, where $\mathrm{ofComplex}$ is the retraction of $\mathbb{C}$ onto $\mathfrak{H}$. Let $j \le n$ and let $\tau \in \mathfrak{H}$. Then the function $z \mapsto \bigl(\partial_{X_1}^{\,j} G(\mathrm{ofComplex}\ z)\bigr)(1, -z)$, obtained by applying the partial derivative $\mathrm{pderiv}\ 1$ with respect to $X_1$ $j$ times and then evaluating at $X_0 = 1$, $X_1 = -z$, has a complex derivative at $\tau$ equal to $$\bigl[j = n\bigr]\, n!\, g(\tau) \;-\; \bigl(\partial_{X_1}^{\,j+1} G(\tau)\bigr)(1, -\tau),$$ the first term being $n!\,g(\tau)$ when $j = n$ and $0$ otherwise.
--
--   This is Bol's identity $\bigl(\tfrac{d}{d\tau}\bigr)^{n+1}\bigl[G(\tau)(1,-\tau)\bigr] = (-1)^n n!\,g(\tau)$ for an Eichler integral $G$ of $g$, recorded one derivative at a time so that only first derivatives of the intermediate quantities $r_j(\tau) = (\partial_{X_1}^{\,j} G(\tau))(1,-\tau)$ occur. It underlies the holomorphy and growth statements [`HeckeEis.IsEichlerIntegral.eq_zero_of_eval_eq_const`](thm.html#HeckeEis.IsEichlerIntegral.eq_zero_of_eval_eq_const) and [`HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval`](thm.html#HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval), and through them the injectivity of the Eichler–Shimura map [`HeckeEis.eichlerShimuraMap_injective`](thm.html#HeckeEis.eichlerShimuraMap_injective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv {n : ℕ} {g : UpperHalfPlane → ℂ}
    {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G) {j : ℕ} (hj : j ≤ n)
    (τ : UpperHalfPlane) :
    HasDerivAt (fun z : ℂ => MvPolynomial.eval ![(1 : ℂ), -z]
        ((MvPolynomial.pderiv 1)^[j]
          ((G (UpperHalfPlane.ofComplex z) : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)))
      ((if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0)
        - MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)]
          ((MvPolynomial.pderiv 1)^[j + 1] ((G τ : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)))
      (τ : ℂ) := by sorry
