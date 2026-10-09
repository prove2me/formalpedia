-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Quasilinear_theorem_4_1
-- name    : HyperbolicBackstepping.Quasilinear.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:21:57.624987+00:00
-- url     : https://prove2.me/theorems/7d071b7e-7558-4162-a062-5bc01537e633
-- title:
--   Theorem 4.1, p. 11 — the backstepping feedback with dynamic extension makes the quasilinear 2 × 2 system locally exponentially stable in H²
-- statement:
--   Consider the quasilinear hyperbolic system $z_t+\Lambda(z,x)z_x+f(z,x)=0$ on $[0,1]\times[0,\infty)$ (2.1) under the standing assumptions of §2: $\Lambda$, $f$, $G_0$ of class $C^2$, $\Lambda(0,x)=\operatorname{diag}(\Lambda_1,\Lambda_2)$ with $\Lambda_1>0>\Lambda_2$, $f(0,x)=0$, $G_0(0)=0$, and assume $q=G_0'(0)\ne0$. Let $(K^{vu},K^{vv})$ be a $C^1$ solution of the kernel equations (3.32), (3.33), (3.36), (3.37) with the coefficients $\epsilon_1=\Lambda_1$, $\epsilon_2=-\Lambda_2$, $c_1=-f_{12}\varphi_1/\varphi_2$, $c_2=-f_{21}\varphi_2/\varphi_1$, and let $k$ be the gain (4.14). Fix $d_1,d_2>0$ with $d_1\ne d_2$, and close the loop with
--   $$z_1(0,t)=G_0(z_2(0,t)),\qquad z_2(1,t)=\int_0^1k^{\mathsf T}(\xi)z(\xi,t)\,d\xi+a(t)+b(t),\qquad \dot a=-d_1a,\quad\dot b=-d_2b .$$
--
--   Then for every rate $\lambda$ with $0<\lambda<2\min(d_1,d_2)$ there exist $\delta>0$ and $c>0$ such that every classical solution $(z,a,b)$ whose initial data satisfy $\|z_0\|_{H^2}\le\delta$ (with $z_0=z(\cdot,0)$), the compatibility conditions (4.16), (4.18), and
--   $$a(0)=\frac{P_2(z_0)-d_2P_1(z_0)}{d_1-d_2},\qquad b(0)=\frac{d_1P_1(z_0)-P_2(z_0)}{d_1-d_2},$$
--   obeys, for all $t\ge0$,
--   $$\|z(\cdot,t)\|_{H^2}^2+a^2(t)+b^2(t)\le c\,e^{-\lambda t}\big(\|z_0\|_{H^2}^2+a^2(0)+b^2(0)\big). \tag{4.27}$$
--
--   This is the main result of the paper: a feedback designed for the linearization by backstepping stabilizes the nonlinear system locally, in the $H^2$ norm $\|z\|_{H^2}=\|z\|_{L^2}+\|z_x\|_{L^2}+\|z_{xx}\|_{L^2}$, and the dynamic extension $(a,b)$ removes the artificial compatibility conditions (4.17), (4.19) that the static feedback (4.15) would impose.
--
--   **Formalization Note** Departures from the printed statement, all disclosed. (1) The page says "for every $\lambda>0$"; for fixed $d_1,d_2$ that is false, since $a(t)=a(0)e^{-d_1t}$ with $a(0)\ne0$ for generic small $z_0$. Lean takes $0<\lambda<2\min(d_1,d_2)$, the range the closing argument (5.71)–(5.72) supports; the printed claim holds in the sense that $d_1,d_2$ may be chosen with $2\min(d_1,d_2)>\lambda$. (2) $\varphi_2$, $C(x)$ and $a(0)$, $b(0)$ are the corrected forms of (4.1), (4.7), (4.26); the page prints $\varphi_2=\exp(-\int f_{22}/\Lambda_2)$, $C=\begin{pmatrix}0&-f_{12}\\-f_{21}&0\end{pmatrix}$, $a(0)=-(P_2+d_2P_1)/(d_1-d_2)$ and $b(0)=(d_1P_1+P_2)/(d_1-d_2)$ (see the closed-loop file). (3) $q\neq0$ is the case the paper treats (p. 9; the case $q=0$ is a remark). (4) Solutions are classical: one $C^2$ function of $(x,t)$ with the equations imposed on $[0,1]\times[0,\infty)$, so this is the theorem restricted to $C^2$ solutions; global existence is not asserted, the statement quantifies over solutions. (5) For a classical solution, (4.16), (4.18) and the values of $a(0)$, $b(0)$ follow from the boundary conditions at $t=0$ and their time derivative; they are kept as hypotheses because the page states them. $\delta$ and $c$ depend only on the data, $d_1$, $d_2$ and $\lambda$, never on the solution.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 11, Theorem 4.1, (4.27)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Quasilinear_ClosedLoop

namespace HyperbolicBackstepping.Quasilinear

theorem theorem_4_1 (P : Plant) (hq : P.q ≠ 0)
    (Kvu Kvv : ℝ → ℝ → ℝ) (hK : HyperbolicBackstepping.Linear.IsVKernel P.ε₁ P.ε₂ P.c₁ P.c₂ P.q Kvu Kvv)
    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd : d₁ ≠ d₂) :
    ∀ lam : ℝ, 0 < lam → lam < 2 * min d₁ d₂ →
      ∃ δ : ℝ, 0 < δ ∧ ∃ c : ℝ, 0 < c ∧
        ∀ (z : ℝ → ℝ → Fin 2 → ℝ) (a b : ℝ → ℝ),
          IsClosedLoopSolution P Kvu Kvv d₁ d₂ z a b →
          a 0 = a₀ P Kvu Kvv d₁ d₂ (fun x => z x 0) →
          b 0 = b₀ P Kvu Kvv d₁ d₂ (fun x => z x 0) →
          H2norm (fun x => z x 0) ≤ δ →
          Compat416 P (fun x => z x 0) →
          Compat418 P (fun x => z x 0) →
          ∀ t : ℝ, 0 ≤ t →
            H2norm (fun x => z x t) ^ 2 + a t ^ 2 + b t ^ 2
              ≤ c * Real.exp (-lam * t) * (H2norm (fun x => z x 0) ^ 2 + a 0 ^ 2 + b 0 ^ 2) := by sorry

end HyperbolicBackstepping.Quasilinear
