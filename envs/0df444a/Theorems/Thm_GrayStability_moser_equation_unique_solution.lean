-- Prove2me | Theorems.Thm_GrayStability_moser_equation_unique_solution
-- name    : GrayStability.moser_equation_unique_solution
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T20:45:52.433384+00:00
-- url     : https://prove2.me/theorems/0ff75e9e-5f86-4980-82e5-465a1a49d292
-- title:
--   Theorem 2.20 (proof): unique solution of the Moser equation (2.1)–(2.2)
-- statement:
--   Let $M=F^{-1}(0)\subset\mathbb{R}^n$ be a compact regular level, $y\in M$, $\alpha$ a contact form at $y$, and $\beta\in(\mathbb{R}^n)^*$ any covector. Then there is exactly one $X\in\xi_y=T_yM\cap\ker\alpha_y$ for which some $\mu\in\mathbb{R}$ satisfies
--   $$\beta(v)+d\alpha_y(X,v)=\mu\,\alpha_y(v)\qquad\text{for all } v\in T_yM.$$
--
--   With $\beta=\dot\alpha_t$ this is equation (2.1), $\dot\alpha_t+i_{X_t}d\alpha_t=\mu_t\alpha_t$; evaluating at the Reeb vector forces $\mu=\beta(R)$, which is (2.2). The unique pointwise solution is the vector field whose flow is the Gray isotopy.
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry Vol. II (2006) 315-382, https://arxiv.org/abs/math/0307242, proof of Theorem 2.20, equations (2.1) and (2.2), p. 15

import Definitions.Def_GrayStability_Basic

namespace GrayStability

/-- Geiges, proof of Theorem 2.20, equations (2.1)–(2.2): at a point where `α` is a
contact form, for every covector `β` there is a unique `X ∈ ξ_y` solving
`β + i_X dα = μ α` on `T_y M` for some `μ ∈ ℝ`. -/
theorem moser_equation_unique_solution {n c : ℕ} (F : E n → (Fin c → ℝ))
    (hF : IsCompactRegularLevel F) (α : OneForm n) (y : E n) (hy : y ∈ levelSet F)
    (hα : IsContactFormAt F α y) (β : E n →L[ℝ] ℝ) :
    ∃! X : E n, X ∈ contactPlane F α y ∧ ∃ μ : ℝ,
      ∀ v ∈ tangentSpace F y, β v + extDerivOneForm α y X v = μ * α y v := by sorry

end GrayStability
