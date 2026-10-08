-- Prove2me | Theorems.Thm_MonoSkew_Main_theorem_3_1
-- name    : MonoSkew.Main.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:10.364859+00:00
-- url     : https://prove2.me/theorems/3524d2ee-fc02-4016-8a0c-fa4624f408b7
-- title:
--   Theorem 3.1 — the inexact primal–dual forward–backward–forward iterates converge weakly to a primal and a dual solution
-- statement:
--   Let $\mathcal H$ and $\mathcal G$ be real Hilbert spaces, let $A:\mathcal H\to2^{\mathcal H}$ and $B:\mathcal G\to2^{\mathcal G}$ be maximally monotone, let $L:\mathcal H\to\mathcal G$ be a nonzero bounded linear operator, and let $z\in\mathcal H$, $r\in\mathcal G$ be such that
--   $$z\in\operatorname{ran}\big(A+L^*\circ B\circ(L\cdot-r)\big).$$
--   Let $(a_{1,n})$, $(b_{1,n})$, $(c_{1,n})$ be absolutely summable sequences in $\mathcal H$ and $(a_{2,n})$, $(b_{2,n})$, $(c_{2,n})$ absolutely summable sequences in $\mathcal G$. Let $x_0\in\mathcal H$, $v_0\in\mathcal G$, $\varepsilon\in\,]0,1/(\|L\|+1)[$, let $(\gamma_n)$ be a sequence in $[\varepsilon,(1-\varepsilon)/\|L\|]$, and for every $n\in\mathbb N$ set
--   $$\begin{aligned}y_{1,n}&=x_n-\gamma_n(L^*v_n+a_{1,n}), & y_{2,n}&=v_n+\gamma_n(Lx_n+a_{2,n}),\\ p_{1,n}&=J_{\gamma_nA}(y_{1,n}+\gamma_nz)+b_{1,n}, & p_{2,n}&=J_{\gamma_nB^{-1}}(y_{2,n}-\gamma_nr)+b_{2,n},\\ q_{1,n}&=p_{1,n}-\gamma_n(L^*p_{2,n}+c_{1,n}), & q_{2,n}&=p_{2,n}+\gamma_n(Lp_{1,n}+c_{2,n}),\\ x_{n+1}&=x_n-y_{1,n}+q_{1,n}, & v_{n+1}&=v_n-y_{2,n}+q_{2,n}.\end{aligned}$$
--   Then there are a solution $\bar x$ of the primal inclusion $z\in A\bar x+L^*B(L\bar x-r)$ and a solution $\bar v$ of the dual inclusion $-r\in -LA^{-1}(z-L^*\bar v)+B^{-1}\bar v$ with $z-L^*\bar v\in A\bar x$ and $\bar v\in B(L\bar x-r)$, such that:
--   1. $x_n-p_{1,n}\to0$ and $v_n-p_{2,n}\to0$;
--   2. $x_n\rightharpoonup\bar x$, $p_{1,n}\rightharpoonup\bar x$, $v_n\rightharpoonup\bar v$ and $p_{2,n}\rightharpoonup\bar v$;
--   3. if $A$ is uniformly monotone at $\bar x$, then $x_n\to\bar x$ and $p_{1,n}\to\bar x$;
--   4. if $B^{-1}$ is uniformly monotone at $\bar v$, then $v_n\to\bar v$ and $p_{2,n}\to\bar v$.
--
--   This is the main result of the paper: a splitting method that uses $A$ and $B$ only through their resolvents (in parallel) and $L$ only through forward applications of $L$ and $L^*$, and that solves the primal and the dual inclusion simultaneously, under the sole existence assumption that the primal problem has a solution.
--
--   **Formalization Note** The resolvents $J_{\gamma_nA}$ and $J_{\gamma_nB^{-1}}$ are given maps, one per $n$, with the resolvent property $\gamma_n^{-1}(w-Jw)\in T(Jw)$; for maximally monotone $A$, $B^{-1}$ and $\gamma_n>0$ they exist and are unique. "Absolutely summable" is $\sum_n\|a_n\|<+\infty$. Convergence in (i), (iii), (iv) is in norm; $\rightharpoonup$ is weak convergence ($\langle u_n,y\rangle\to\langle u,y\rangle$ for every $y$). The same pair $(\bar x,\bar v)$ serves all four clauses; uniform monotonicity is assumed at that point. The paper's "in Problem 1.1" (both operators maximally monotone, $L$ bounded linear) and the completeness of $\mathcal H$, $\mathcal G$ are explicit hypotheses; $\|L\|$ is the operator norm, and $L\neq0$ is kept as printed.
-- source:
--   Briceño-Arias and Combettes, A Monotone+Skew Splitting Model for Composite Monotone Inclusions in Duality, arXiv:1011.5517v1, pp. 10–11, Theorem 3.1, (3.1)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_MonoSkew_Main_Basic

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

namespace MonoSkew.Main

/-- Theorem 3.1 (pp. 10–11): in Problem 1.1 with `L ≠ 0` and
`z ∈ ran(A + L* ∘ B ∘ (L · − r))`, the iterates of the inexact primal–dual
forward–backward–forward method (3.1) with absolutely summable errors and step sizes in
`[ε, (1 − ε)/‖L‖]` satisfy, for some primal solution `x̄` and dual solution `v̄` with
`z − L*v̄ ∈ Ax̄` and `v̄ ∈ B(Lx̄ − r)`: (i) `x_n − p_{1,n} → 0`, `v_n − p_{2,n} → 0`;
(ii) `x_n, p_{1,n} ⇀ x̄` and `v_n, p_{2,n} ⇀ v̄`; (iii) if `A` is uniformly monotone at `x̄`
then `x_n, p_{1,n} → x̄`; (iv) if `B⁻¹` is uniformly monotone at `v̄` then `v_n, p_{2,n} → v̄`. -/
theorem theorem_3_1 {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : H → Set H) (B : G → Set G) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (L : H →L[ℝ] G) (z : H) (r : G)
    (hL : L ≠ 0) (hran : ∃ x, z ∈ primalOp A B L r x)
    (a₁ b₁ c₁ : ℕ → H) (a₂ b₂ c₂ : ℕ → G)
    (ha₁ : Summable (fun n => ‖a₁ n‖)) (hb₁ : Summable (fun n => ‖b₁ n‖))
    (hc₁ : Summable (fun n => ‖c₁ n‖))
    (ha₂ : Summable (fun n => ‖a₂ n‖)) (hb₂ : Summable (fun n => ‖b₂ n‖))
    (hc₂ : Summable (fun n => ‖c₂ n‖))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / (‖L‖ + 1))
    (γ : ℕ → ℝ) (hγ : ∀ n, ε ≤ γ n ∧ γ n ≤ (1 - ε) / ‖L‖)
    (JA : ℕ → H → H) (hJA : ∀ n, IsResolvent (γ n) A (JA n))
    (JBinv : ℕ → G → G) (hJB : ∀ n, IsResolvent (γ n) (opInv B) (JBinv n))
    (x y₁ p₁ q₁ : ℕ → H) (v y₂ p₂ q₂ : ℕ → G)
    (hrun : IsPDRun L z r γ JA JBinv a₁ b₁ c₁ a₂ b₂ c₂ x y₁ p₁ q₁ v y₂ p₂ q₂) :
    ∃ xbar : H, ∃ vbar : G,
      xbar ∈ primalSet A B L z r ∧ vbar ∈ dualSet A B L z r ∧
      z - ContinuousLinearMap.adjoint L vbar ∈ A xbar ∧ vbar ∈ B (L xbar - r) ∧
      (Tendsto (fun n => x n - p₁ n) atTop (𝓝 0) ∧
        Tendsto (fun n => v n - p₂ n) atTop (𝓝 0)) ∧
      (WeakTendsto x xbar ∧ WeakTendsto p₁ xbar ∧ WeakTendsto v vbar ∧
        WeakTendsto p₂ vbar) ∧
      (IsUniformlyMonotoneAt A xbar →
        Tendsto x atTop (𝓝 xbar) ∧ Tendsto p₁ atTop (𝓝 xbar)) ∧
      (IsUniformlyMonotoneAt (opInv B) vbar →
        Tendsto v atTop (𝓝 vbar) ∧ Tendsto p₂ atTop (𝓝 vbar)) := by sorry

end MonoSkew.Main
