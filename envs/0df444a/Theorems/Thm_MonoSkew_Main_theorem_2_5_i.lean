-- Prove2me | Theorems.Thm_MonoSkew_Main_theorem_2_5_i
-- name    : MonoSkew.Main.theorem_2_5_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:08.142772+00:00
-- url     : https://prove2.me/theorems/8b4d88be-ada1-43c7-97c6-6f4243c4eb71
-- title:
--   Theorem 2.5(i) — the inexact forward–backward–forward residuals $\|x_n-p_n\|$ and $\|y_n-q_n\|$ are square summable
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, let $A:\mathcal H\to2^{\mathcal H}$ be maximally monotone, and let $B:\mathcal H\to\mathcal H$ be monotone. Suppose that $\operatorname{zer}(A+B)\neq\varnothing$ and that $B$ is $\beta$-Lipschitzian for some $\beta\in\,]0,+\infty[$. Let $(a_n)$, $(b_n)$, $(c_n)$ be sequences in $\mathcal H$ with
--   $$\sum_{n}\|a_n\|<+\infty,\qquad\sum_n\|b_n\|<+\infty,\qquad\sum_n\|c_n\|<+\infty,$$
--   let $x_0\in\mathcal H$, let $\varepsilon\in\,]0,1/(\beta+1)[$, let $(\gamma_n)$ be a sequence in $[\varepsilon,(1-\varepsilon)/\beta]$, and set, for every $n\in\mathbb N$,
--   $$y_n=x_n-\gamma_n(Bx_n+a_n),\quad p_n=J_{\gamma_nA}y_n+b_n,\quad q_n=p_n-\gamma_n(Bp_n+c_n),\quad x_{n+1}=x_n-y_n+q_n,$$
--   where $J_{\gamma A}=(\mathrm{Id}+\gamma A)^{-1}$ is the resolvent. Then
--   $$\sum_{n\in\mathbb N}\|x_n-p_n\|^2<+\infty\qquad\text{and}\qquad\sum_{n\in\mathbb N}\|y_n-q_n\|^2<+\infty.$$
--
--   This is the energy estimate of the inexact forward–backward–forward (Tseng) method; the main theorem of the paper applies it on the product space $\mathcal H\oplus\mathcal G$.
--
--   **Formalization Note** The resolvent $J_{\gamma_nA}$ is a given map $J_n$ with the resolvent property $\gamma_n^{-1}(x-J_nx)\in A(J_nx)$ for all $x$, one map per $n$ since $\gamma_n$ varies; for maximally monotone $A$ and $\gamma_n>0$ this map exists and is unique. Monotonicity of $B$ is monotonicity of the operator $x\mapsto\{Bx\}$; $\operatorname{zer}(A+B)=\{x\mid 0\in Ax+Bx\}$. The space is a generic real Hilbert space (completeness explicit), so the statement applies to $\mathcal H\oplus\mathcal G$. Clause (i) does not involve the point $\bar x$ of the theorem's lead-in.
-- source:
--   Briceño-Arias and Combettes, A Monotone+Skew Splitting Model for Composite Monotone Inclusions in Duality, arXiv:1011.5517v1, p. 5, Theorem 2.5(i), (2.2), (2.3)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_MonoSkew_Main_Basic

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

namespace MonoSkew.Main

/-- Theorem 2.5(i) (p. 5): for the inexact forward–backward–forward iteration (2.3) with
absolutely summable errors and step sizes in `[ε, (1 − ε)/β]`,
`Σ ‖x_n − p_n‖² < ∞` and `Σ ‖y_n − q_n‖² < ∞`. -/
theorem theorem_2_5_i {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E → Set E) (hA : IsMaximalMonotone A)
    (B : E → E) (hB : IsMonotoneOp (fun u => ({B u} : Set E)))
    (hzer : (zer (addSingle A B)).Nonempty)
    (β : ℝ) (hβ : 0 < β) (hBlip : ∀ u w : E, ‖B u - B w‖ ≤ β * ‖u - w‖)
    (a b c : ℕ → E) (ha : Summable (fun n => ‖a n‖)) (hb : Summable (fun n => ‖b n‖))
    (hc : Summable (fun n => ‖c n‖))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / (β + 1))
    (γ : ℕ → ℝ) (hγ : ∀ n, ε ≤ γ n ∧ γ n ≤ (1 - ε) / β)
    (J : ℕ → E → E) (hJ : ∀ n, IsResolvent (γ n) A (J n))
    (x y p q : ℕ → E) (hrun : IsFBFRun B γ J a b c x y p q) :
    Summable (fun n => ‖x n - p n‖ ^ 2) ∧ Summable (fun n => ‖y n - q n‖ ^ 2) := by sorry

end MonoSkew.Main
