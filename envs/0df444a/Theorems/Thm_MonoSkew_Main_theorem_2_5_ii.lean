-- Prove2me | Theorems.Thm_MonoSkew_Main_theorem_2_5_ii
-- name    : MonoSkew.Main.theorem_2_5_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:01.145149+00:00
-- url     : https://prove2.me/theorems/8e930f13-4408-4d42-9c3d-24e80ca64486
-- title:
--   Theorem 2.5(ii) — the inexact forward–backward–forward iterates $x_n$ and $p_n$ converge weakly to a zero of $A+B$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, let $A:\mathcal H\to2^{\mathcal H}$ be maximally monotone, and let $B:\mathcal H\to\mathcal H$ be monotone. Suppose that $\operatorname{zer}(A+B)\neq\varnothing$ and that $B$ is $\beta$-Lipschitzian for some $\beta\in\,]0,+\infty[$. Let $(a_n)$, $(b_n)$, $(c_n)$ be absolutely summable sequences in $\mathcal H$, let $x_0\in\mathcal H$, let $\varepsilon\in\,]0,1/(\beta+1)[$, let $(\gamma_n)$ be a sequence in $[\varepsilon,(1-\varepsilon)/\beta]$, and set, for every $n\in\mathbb N$,
--   $$y_n=x_n-\gamma_n(Bx_n+a_n),\quad p_n=J_{\gamma_nA}y_n+b_n,\quad q_n=p_n-\gamma_n(Bp_n+c_n),\quad x_{n+1}=x_n-y_n+q_n.$$
--   Then there is $\bar x\in\operatorname{zer}(A+B)$ such that
--   $$x_n\rightharpoonup\bar x\qquad\text{and}\qquad p_n\rightharpoonup\bar x.$$
--
--   This is the weak convergence of the inexact forward–backward–forward method with variable step sizes and summable errors; it is the engine of the paper's main theorem.
--
--   **Formalization Note** The resolvent $J_{\gamma_nA}$ is a given map $J_n$ with $\gamma_n^{-1}(x-J_nx)\in A(J_nx)$ for all $x$, one per $n$. Weak convergence $u_n\rightharpoonup u$ means $\langle u_n,y\rangle\to\langle u,y\rangle$ for every $y$. Completeness of $\mathcal H$ is explicit; monotonicity of $B$ is monotonicity of $x\mapsto\{Bx\}$.
-- source:
--   Briceño-Arias and Combettes, A Monotone+Skew Splitting Model for Composite Monotone Inclusions in Duality, arXiv:1011.5517v1, p. 5, Theorem 2.5(ii), (2.2), (2.3)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_MonoSkew_Main_Basic

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

namespace MonoSkew.Main

/-- Theorem 2.5(ii) (p. 5): for the inexact forward–backward–forward iteration (2.3), there is
`x̄ ∈ zer(A + B)` with `x_n ⇀ x̄` and `p_n ⇀ x̄`. -/
theorem theorem_2_5_ii {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
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
    ∃ xbar ∈ zer (addSingle A B), WeakTendsto x xbar ∧ WeakTendsto p xbar := by sorry

end MonoSkew.Main
