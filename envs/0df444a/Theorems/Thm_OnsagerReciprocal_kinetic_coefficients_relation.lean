-- Prove2me | Theorems.Thm_OnsagerReciprocal_kinetic_coefficients_relation
-- name    : OnsagerReciprocal.kinetic_coefficients_relation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:58:37.625786+00:00
-- url     : https://prove2.me/theorems/ac2bfe13-a6a6-4c07-955e-efbefa67fcc1
-- title:
--   Kinetic coefficients: $\dot x=-\lambda x=-\gamma X$
-- statement:
--   Let $\beta$ be a positive definite real symmetric $n\times n$ matrix and $\lambda$ any real $n\times n$ matrix. Put $X=\beta x$ and $\gamma=\lambda\beta^{-1}$. Then for every $x\in\mathbb R^n$,
--   $$-\lambda x=-\gamma X .$$
--   That is, the quasi-stationary relaxation law $\dot x_i=-\lambda_{ik}x_k$ can be rewritten in terms of the conjugate quantities as $\dot x_i=-\gamma_{ik}X_k$, which is how the kinetic coefficients $\gamma_{ik}$ are introduced.
-- source:
--   Wikipedia, "Onsager reciprocal relations", https://en.wikipedia.org/w/index.php?title=Onsager_reciprocal_relations&oldid=1355014688, section "Abstract formulation" and its "Proof" subsection (pp. 5-6 of the PDF export), following L. D. Landau, E. M. Lifshitz, Statistical Physics, Part 1 (1975)

import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix

namespace OnsagerReciprocal
theorem kinetic_coefficients_relation {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (x : Fin n → ℝ) :
    -(lam *ᵥ x) = -(kineticCoeff β lam *ᵥ conjugate β x) := by sorry
end OnsagerReciprocal
