-- Prove2me | Theorems.Thm_OTDRO_Dual_sup_transport_eq_ellRob
-- name    : OTDRO.Dual.sup_transport_eq_ellRob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:32.896181+00:00
-- url     : https://prove2.me/theorems/e092e151-b6fd-401d-b440-5aae1989e173
-- title:
--   Equation (25), p. 32 — transport envelope equals robust loss
-- statement:
--   Fix $x\in\mathbb R^d$ with $A(x)$ positive definite, a loss $\ell$, a radius $\delta>0$, a vector $\beta$, and a new multiplier $\lambda\ge0$. Rescale the original transport multiplier as $\lambda/\sqrt\delta$. Then
--
--   $$\sup_{\Delta\in\mathbb R^d}\left\{\ell\bigl(\beta^{\mathsf T}(x+\Delta)\bigr)-\frac{\lambda}{\sqrt\delta}\bigl(\Delta^{\mathsf T}A(x)\Delta-\delta\bigr)\right\}=\ell_{\rm rob}(\beta,\lambda;x).$$
--
--   The identity is the pointwise change of variables in equation (25), connecting the published transport dual envelope to the paper's $F$ and $f_\delta$ notation.
--
--   **Formalization Note** Both sides are extended real suprema. The statement includes $\beta=0$, for which the value is $\ell(0)+\lambda\sqrt\delta$. The two multipliers are visibly distinguished by the factor $1/\sqrt\delta$.
-- source:
--   arXiv:1810.02403v3, §5.1, proof of Theorem 1, p. 32, (25)

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

namespace OTDRO.Dual

open Matrix

/-- Equation (25), p. 32, with the old transport multiplier `lam / √δ` and the new
multiplier `lam` in `Fobj` distinguished explicitly. -/
theorem sup_transport_eq_ellRob {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hQ : (A x).PosDef)
    (ℓ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (hlam : 0 ≤ lam) :
    (⨆ Δ : EuclideanSpace ℝ (Fin d),
      ((ℓ (inner ℝ β (x + Δ)) - (lam / Real.sqrt δ) *
        (dotProduct Δ.ofLp (A x *ᵥ Δ.ofLp) - δ) : ℝ) : EReal)) =
      ellRob ℓ A δ β lam x := by sorry

end OTDRO.Dual
