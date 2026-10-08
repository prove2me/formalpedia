-- Prove2me | Theorems.Thm_Katyusha_SC_lemma_2_3
-- name    : Katyusha.SC.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:35:43.767303+00:00
-- url     : https://prove2.me/theorems/ee910e68-27f8-4ef8-a479-de723cf54058
-- title:
--   Lemma 2.3 — proximal gradient descent
-- statement:
--   Let $f=n^{-1}\sum_{i=1}^n f_i$ and $F=f+\psi$ on $\mathbb R^d$, with $n\ge1$, $L,\sigma>0$, convex $L$ smooth components $f_i$ with their actual gradients, and a $\sigma$ strongly convex regularizer $\psi$. For a fixed snapshot $\widetilde x$ and point $x$, the estimator from a uniform index $i$ is $\widetilde\nabla_i=\nabla f(\widetilde x)+\nabla f_i(x)-\nabla f_i(\widetilde x)$.
--
--   Let $y_i^+$ minimize the Option I proximal objective at $x$ with gradient $\widetilde\nabla_i$, and let $\operatorname{Prog}_i$ be the negative value of that objective relative to $x$ at this minimizer. Then $\operatorname{Prog}_i\ge0$ for every $i$, and
--   $$F(x)-\mathbb E_i F(y_i^+)\ge\mathbb E_i\operatorname{Prog}_i-\frac1{4L}\mathbb E_i\|\nabla f(x)-\widetilde\nabla_i\|^2.$$
--   The estimate isolates the objective decrease of the proximal step and its variance penalty.
--
--   **Formalization Note** The progression value is evaluated at the proximal minimizer, avoiding an infimum with a default value. Expectation is a finite uniform average over $i\in\{1,\dots,n\}$.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, p. 8, Lemma 2.3

import Definitions.Def_Katyusha_SC_run

namespace Katyusha.SC

/-- Lemma 2.3, p. 8: averaged proximal descent with the estimator's variance penalty. -/
theorem lemma_2_3 {d n : ℕ} (p : Problem d n) (P : ℝ → Vec d → Vec d)
    (hp : IsValid p) (hP : IsProxMap p.ψ P) (snapshot x : Vec d) :
    (∀ i : Fin n, 0 ≤ progress p P snapshot x i) ∧
    objective p x - (1 / (n : ℝ)) * ∑ i, objective p (nextY p P snapshot x i) ≥
      (1 / (n : ℝ)) * ∑ i, progress p P snapshot x i -
      1 / (4 * p.smoothness) * ((1 / (n : ℝ)) * ∑ i,
        ‖SAGA.Convex.gradAvg p.grad x - estimator p snapshot x i‖ ^ 2) := by sorry

end Katyusha.SC
