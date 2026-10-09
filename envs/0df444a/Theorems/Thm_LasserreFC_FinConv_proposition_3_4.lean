-- Prove2me | Theorems.Thm_LasserreFC_FinConv_proposition_3_4
-- name    : LasserreFC.FinConv.proposition_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:33:29.549785+00:00
-- url     : https://prove2.me/theorems/11e86962-b427-417b-88c4-d4fc8d3dbb51
-- title:
--   Proposition 3.4, p. 9 — if (1.2) attains its value and (1.3) fails at a global minimizer, there is no finite convergence
-- statement:
--   Suppose the relaxation (1.2) achieves its optimal value: at every order $k$ with $f_k$ finite there is $\gamma = f_k$ with $f - \gamma \in \langle h\rangle_{2k} + Q_k(g)$. Let $f_{\min}$ be the minimum of (1.1) and let $u$ be a global minimizer at which the first order optimality condition (1.3) fails, i.e. there are no $\lambda \in \mathbb R^{m_1}$, $\mu \in \mathbb R^{m_2}$ with $\nabla f(u) = \sum_i \lambda_i \nabla h_i(u) + \sum_j \mu_j \nabla g_j(u)$. Then
--
--   $$f_k \ne f_{\min} \quad \text{for every } k \in \mathbb N,$$
--
--   i.e. Lasserre's hierarchy cannot have finite convergence.
--
--   This is the converse direction to Theorem 1.1: the first order condition is necessary for finite convergence whenever the relaxations attain their values.
--
--   **Formalization Note** "(1.2) achieves its optimal value" is required at every order where $f_k$ is finite, which is where the proof uses it. "(1.3) fails" is the failure of the gradient equation (1.3) alone, with no sign condition on $\mu$.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 9, Proposition 3.4

import Mathlib
import Definitions.Def_LasserreFC_FinConv_Setting
import Definitions.Def_LasserreFC_FinConv_Hierarchy

namespace LasserreFC.FinConv

open MvPolynomial

/-- Proposition 3.4, p. 9: if (1.2) achieves its optimal value (at every order where it is finite) and
the first order optimality condition (1.3) fails at a global minimizer of (1.1), then Lasserre's
hierarchy cannot have finite convergence. -/
theorem proposition_3_4 {n m1 m2 : ℕ} (P : POP n m1 m2)
    (hatt : ∀ k : ℕ, lasserreValue P k ≠ ⊥ → lasserreValue P k ≠ ⊤ →
      ∃ γ : ℝ, (γ : EReal) = lasserreValue P k ∧ P.f - C γ ∈ trunc P k)
    (fmin : ℝ) (hfmin : IsLeast ((fun x => eval x P.f) '' P.K) fmin)
    (u : Fin n → ℝ) (hu : u ∈ P.K) (hmin : IsMinOn (fun x => eval x P.f) P.K u)
    (hfooc : ¬ ∃ (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ),
      grad P.f u = ∑ i, lam i • grad (P.h i) u + ∑ j, mu j • grad (P.g j) u) :
    ∀ k : ℕ, lasserreValue P k ≠ (fmin : EReal) := by sorry

end LasserreFC.FinConv
