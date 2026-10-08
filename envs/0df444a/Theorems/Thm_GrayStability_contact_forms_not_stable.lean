-- Prove2me | Theorems.Thm_GrayStability_contact_forms_not_stable
-- name    : GrayStability.contact_forms_not_stable
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T21:32:02.179411+00:00
-- url     : https://prove2.me/theorems/376b3fba-dac5-4359-b760-d11f7c543f84
-- title:
--   Remark 2.21(1): contact forms are not stable
-- statement:
--   Let $\alpha_t=(x_1\,dy_1-y_1\,dx_1)+(1+t)(x_2\,dy_2-y_2\,dx_2)$ on the unit sphere $S^3\subset\mathbb{R}^4$. There is no isotopy $\psi_t$ of $S^3$, $t\in[0,1]$, with
--   $$\psi_t^*\alpha_t=\alpha_0\quad\text{on } TS^3\ \text{ for all } t\in[0,1].$$
--
--   So the conformal factor $\lambda_t$ in Gray's theorem cannot be removed: stability holds for contact structures, not for contact forms. The obstruction is dynamical: such a $\psi_t$ would conjugate the Reeb flows of $\alpha_0$ (all orbits closed) and $\alpha_t$ (two closed orbits for irrational $t$).
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry Vol. II (2006) 315-382, https://arxiv.org/abs/math/0307242, Remark 2.21 (1), p. 15

import Definitions.Def_GrayStability_HopfFamily

namespace GrayStability

/-- Geiges, Remark 2.21 (1): contact forms are not stable. For the family
`α_t = (x₁ dy₁ - y₁ dx₁) + (1 + t)(x₂ dy₂ - y₂ dx₂)` on `S³` there is no isotopy
`ψ_t`, `t ∈ [0, 1]`, with `ψ_t^* α_t = α_0`. -/
theorem contact_forms_not_stable :
    ¬ ∃ ψ : ℝ → E 4 → E 4, IsIsotopyOf unitSphereEquation ψ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet unitSphereEquation,
        ∀ v ∈ tangentSpace unitSphereEquation y,
          pullback (ψ t) (hopfFamily t) y v = hopfFamily 0 y v := by sorry

end GrayStability
