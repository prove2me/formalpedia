-- Prove2me | Theorems.Thm_ModularCurve_exists_cuspForm_petersson_eq_of_finiteIndex
-- name    : ModularCurve.exists_cuspForm_petersson_eq_of_finiteIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/ad568809-b8a8-5a92-994b-23d60d40ebba
-- title:
--   Petersson pairing represents every functional on S₂(Γ)
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of finite index, and let $\ell$ be a $\mathbb{C}$-linear functional on the space $\mathrm{CuspForm}\ \Gamma\ 2$ of weight-two cusp forms for $\Gamma$. Then there is a cusp form $f \in \mathrm{CuspForm}\ \Gamma\ 2$ such that for every $g \in \mathrm{CuspForm}\ \Gamma\ 2$ one has
--   $$i \int_{\mathcal{F}_\Gamma} \mathrm{petersson}\,2\,f\,g\,(\tau) \;=\; \ell(g),$$
--   where the integrand is the weight-two Petersson integrand $\overline{f(\tau)}\,g(\tau)\,(\operatorname{Im}\tau)^{2}$ and the domain of integration is the set
--   $$\mathcal{F}_\Gamma \;=\; \bigcup_{q \in \mathrm{SL}_2(\mathbb{Z})/\Gamma} \sigma_q^{-1}\cdot \mathcal{D} \subseteq \mathbb{H},$$
--   the union, over the cosets $q$ of $\Gamma$ in $\mathrm{SL}_2(\mathbb{Z})$, of the translates of the standard fundamental domain $\mathcal{D}$ for the modular group by the inverse of a chosen representative $\sigma_q$ of $q$. Only existence of such an $f$ is asserted: no uniqueness, and no separate claim of integrability, positivity or sesquilinearity of the pairing, are part of the conclusion.
--
--   This is the Riesz representation statement for the Petersson pairing in weight two on a finite-index subgroup: since $S_2(\Gamma)$ is finite-dimensional, the positive-definite Petersson pairing identifies it with its dual. It is used in the study of period lattices of weight-two forms, in particular by [`ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int`](thm.html#ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int); finite-dimensionality enters through [`CuspForm.finiteDimensional_of_isArithmetic`](thm.html#CuspForm.finiteDimensional_of_isArithmetic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_cuspForm_petersson_eq_of_finiteIndex.lean

import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_cuspForm_petersson_eq_of_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (ℓ : Module.Dual ℂ (CuspForm Γ 2)) :
    ∃ f : CuspForm Γ 2,
      ∀ g : CuspForm Γ 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
          UpperHalfPlane.petersson 2 f g τ) = ℓ g := by sorry
