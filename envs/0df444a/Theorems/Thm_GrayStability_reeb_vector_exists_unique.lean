-- Prove2me | Theorems.Thm_GrayStability_reeb_vector_exists_unique
-- name    : GrayStability.reeb_vector_exists_unique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T20:07:36.983927+00:00
-- url     : https://prove2.me/theorems/6d413c52-c472-4947-9c8b-bf2f00914d88
-- title:
--   Definition 2.5: existence and uniqueness of the Reeb vector
-- statement:
--   Let $M=F^{-1}(0)\subset\mathbb{R}^n$ be a compact regular level, $y\in M$, and let $\alpha$ be a one-form that is a contact form at $y$. Then there is exactly one vector $R\in T_yM$ with
--   $$\alpha_y(R)=1\qquad\text{and}\qquad d\alpha_y(R,v)=0\ \text{ for all } v\in T_yM.$$
--
--   $R$ is the Reeb vector of $\alpha$ at $y$. It exists because $d\alpha_y|_{T_yM}$ is a skew form of maximal rank on an odd-dimensional space, so its kernel is a line, and the contact condition makes $\alpha$ non-zero on that line.
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry Vol. II (2006) 315-382, https://arxiv.org/abs/math/0307242, Definition 2.5 and the paragraph after it, p. 6

import Definitions.Def_GrayStability_Basic

namespace GrayStability

/-- Geiges, Definition 2.5 and the paragraph after it: at a point of `M` where `α` is
a contact form there is a unique Reeb vector `R ∈ T_y M`, `α(R) = 1`,
`dα(R, ·) = 0` on `T_y M`. -/
theorem reeb_vector_exists_unique {n c : ℕ} (F : E n → (Fin c → ℝ))
    (hF : IsCompactRegularLevel F) (α : OneForm n) (y : E n) (hy : y ∈ levelSet F)
    (hα : IsContactFormAt F α y) :
    ∃! R : E n, R ∈ tangentSpace F y ∧ α y R = 1 ∧
      ∀ v ∈ tangentSpace F y, extDerivOneForm α y R v = 0 := by sorry

end GrayStability
