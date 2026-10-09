-- Prove2me | Theorems.Thm_NesterovODE_WellPosed_lemma_20
-- name    : NesterovODE.WellPosed.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:41:14.390217+00:00
-- url     : https://prove2.me/theorems/14324b06-3e1e-44cf-9c9c-39028045dcac
-- title:
--   Lemma 20, p. 31 — gradient difference for two local solutions
-- statement:
--   Suppose $f\in\mathcal F_L$, and $X,Y$ are two solutions of (3) with the same initial position and zero initial velocity on $0<t<a$. Let $\widetilde M(t)=\sup_{0\le u<t}\|\dot X(u)-\dot Y(u)\|$. Then for $0<t<a$,
--   $$
--   \|\nabla f(X(t))-\nabla f(Y(t))\|\le Lt\,\widetilde M(t).
--   $$
--   This controls the difference in the forcing terms near the initial time.
--
--   **Formalization Note** Any $B$ that bounds the velocity difference at every $0\le u<t$ replaces the supremum in Lean. The local solution predicate includes the common initial data and the one-sided regularity at zero.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 31, Lemma 20

import Mathlib
import Definitions.Def_NesterovODE_WellPosed_Setting

namespace NesterovODE.WellPosed

/-- Lemma 20, p. 31: gradient variation between two local solutions. -/
theorem lemma_20 {n : ℕ} (f : E n → ℝ) (L : NNReal) (x₀ : E n)
    (a t B : ℝ) (X V Y W : ℝ → E n)
    (hf : IsFL f L) (hX : IsLocalSolution f x₀ a X V)
    (hY : IsLocalSolution f x₀ a Y W)
    (ht₀ : 0 < t) (hta : t < a)
    (hB : ∀ u : ℝ, 0 ≤ u → u < t → ‖V u - W u‖ ≤ B) :
    ‖gradient f (X t) - gradient f (Y t)‖ ≤ (L : ℝ) * t * B := by sorry

end NesterovODE.WellPosed
