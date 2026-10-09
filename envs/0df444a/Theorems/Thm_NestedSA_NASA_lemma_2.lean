-- Prove2me | Theorems.Thm_NestedSA_NASA_lemma_2
-- name    : NestedSA.NASA.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:39:58.875843+00:00
-- url     : https://prove2.me/theorems/16043435-b9d9-4f22-bf87-6def7d8d51cc
-- title:
--   Lemma 2 — ∇(f∘g) is Lipschitz with constant L_g² L_∇f + L_f L_∇g
-- statement:
--   Let $f:\mathbb R^m\to\mathbb R$ and $g:\mathbb R^n\to\mathbb R^m$ satisfy Assumption 2: both are continuously differentiable, and $f$, $g$, $\nabla f$, $\nabla g$ are Lipschitz with constants $L_f$, $L_g$, $L_{\nabla f}$, $L_{\nabla g}$. Then the gradient of $F=f\circ g$ is Lipschitz continuous: for all $x,\hat x\in\mathbb R^n$,
--   $$\|\nabla F(x)-\nabla F(\hat x)\|\le\big(L_g^2L_{\nabla f}+L_fL_{\nabla g}\big)\|x-\hat x\|.$$
--
--   This supplies the smoothness constant $L_{\nabla F}$ used in the descent step of the merit-function analysis.
--
--   **Formalization Note** The paper's proof starts from $x,\hat x\in X$; since Assumption 2 is global, the statement is made on all of $\mathbb R^n$.
-- source:
--   Ghadimi, Ruszczyński, Wang, A Single Time-Scale Stochastic Approximation Method for Nested Stochastic Optimization, arXiv:1812.01094v2, p. 9, Lemma 2

import Mathlib
import Definitions.Def_NestedSA_NASA_Basic
import Definitions.Def_NestedSA_NASA_Model

namespace NestedSA.NASA

/-- Lemma 2 (p. 9): under Assumption 2 the gradient of `F = f ∘ g` is Lipschitz continuous on all of `ℝⁿ` with
constant `L_∇F = L_g² L_∇f + L_f L_∇g`. -/
theorem lemma_2 {n m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (Lf Lg Ldf Ldg : ℝ)
    (hA2 : Assumption2 f g Lf Lg Ldf Ldg) (x x' : EuclideanSpace ℝ (Fin n)) :
    ‖gradF f g x - gradF f g x'‖ ≤ LgradF Lf Lg Ldf Ldg * ‖x - x'‖ := by sorry

end NestedSA.NASA
