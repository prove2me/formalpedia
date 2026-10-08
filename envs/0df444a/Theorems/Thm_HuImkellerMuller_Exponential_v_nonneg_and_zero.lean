-- Prove2me | Theorems.Thm_HuImkellerMuller_Exponential_v_nonneg_and_zero
-- name    : HuImkellerMuller.Exponential.v_nonneg_and_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:01.58592+00:00
-- url     : https://prove2.me/theorems/3507df1e-80f6-458d-8fc7-c8f622732247
-- title:
--   p. 8 — for f = −(α/2)dist²(z + θ/α, C) + zθ + |θ|²/(2α): v(p, z) ≥ 0 on C and v = 0 on Π_C(z + θ/α)
-- statement:
--   Let $C\subseteq\mathbb R^m$ be closed, $\theta,z\in\mathbb R^m$ and $\alpha>0$. Set
--   $$f(z)=-\frac{\alpha}{2}\operatorname{dist}^2\Big(z+\frac1\alpha\theta,\,C\Big)+z\theta+\frac{1}{2\alpha}|\theta|^2,\qquad v(p,z)=-\alpha p\theta+\alpha f(z)+\tfrac12\alpha^2|p-z|^2 .$$
--   Then
--
--   1. $v(p,z)\ge0$ for every $p\in C$;
--   2. $v(p^*,z)=0$ for every $p^*\in\Pi_C\big(z+\frac1\alpha\theta\big)$.
--
--   This is the computation that dictates the choice of the driver $f$: the process $\tilde A^{(p)}=-\exp\big(\int_0^\cdot v(s,p_s,Z_s)\,ds\big)$ is then nonincreasing for every admissible $p$ and constant for a selection $p^*$ of nearest points.
--
--   **Formalization Note** The page states the claim for $v(t,p,z)$ with $C=C_t(\omega)$ and $\theta=\theta_t$; it is stated here pointwise for a fixed closed set and fixed vectors, which is the content of the computation. The hypothesis $p\in C$ in part 1 is explicit (the page's derivation is for strategies with $p_t\in C_t$).
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, §2, p. 8, display v(t,p,z) and the sentence after "Now set f(t,z) = …"

import Mathlib
import Definitions.Def_HuImkellerMuller_Exponential_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Exponential

/-- p. 8: with f(z) = −(α/2) dist²(z + θ/α, C) + zθ + |θ|²/(2α) and
v(p, z) = −αpθ + αf(z) + ½α²|p − z|², one has v(p, z) ≥ 0 for p ∈ C and v(p*, z) = 0 for
p* ∈ Π_C(z + θ/α). -/
theorem v_nonneg_and_zero {m : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin m))) (hC : IsClosed C)
    (θ z : EuclideanSpace ℝ (Fin m)) (α : ℝ) (hα : 0 < α) :
    (∀ p ∈ C, 0 ≤ vfun C θ α p z) ∧
      ∀ p ∈ proj C (z + (1 / α) • θ), vfun C θ α p z = 0 := by sorry

end HuImkellerMuller.Exponential
