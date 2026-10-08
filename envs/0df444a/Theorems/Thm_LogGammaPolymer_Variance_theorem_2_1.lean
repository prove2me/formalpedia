-- Prove2me | Theorems.Thm_LogGammaPolymer_Variance_theorem_2_1
-- name    : LogGammaPolymer.Variance.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:47.162557+00:00
-- url     : https://prove2.me/theorems/dd229e8d-0a4f-443d-be6d-6f5cce017d31
-- title:
--   Theorem 2.1 — C₁N^{2/3} ≤ Var(log Z_{m,n}) ≤ C₂N^{2/3} in the characteristic direction
-- statement:
--   Let $0<\theta<\mu$ and assume (2.4): the weights $\{U_{i,0},V_{0,j},Y_{i,j}: i,j\in\mathbb N\}$ are independent with $U_{i,0}^{-1}\sim\mathrm{Gamma}(\theta,1)$, $V_{0,j}^{-1}\sim\mathrm{Gamma}(\mu-\theta,1)$ and $Y_{i,j}^{-1}\sim\mathrm{Gamma}(\mu,1)$. Let $N\ge1$ be real, $\gamma$ a constant, and let $(m,n)$ satisfy
--   $$|m-N\Psi_1(\mu-\theta)|\le\gamma N^{2/3}\quad\text{and}\quad|n-N\Psi_1(\theta)|\le\gamma N^{2/3}\qquad(2.6).$$
--   Then there exist constants $0<C_1,C_2<\infty$, depending on $\theta,\mu,\gamma$, such that
--   $$C_1N^{2/3}\le\mathrm{Var}\bigl(\log Z_{m,n}\bigr)\le C_2N^{2/3},$$
--   where the upper bound holds for all $N\ge1$ and the lower bound for all $N\ge N_0$, with $N_0$ depending on $\theta,\mu,\gamma$.
--
--   This is the main result of the paper: in the characteristic direction the free energy of the log-gamma polymer with boundary conditions has fluctuations of order $N^{1/3}$, the exponent predicted by KPZ universality, proved here for a positive-temperature directed polymer.
--
--   **Formalization Note** The printed theorem asserts the lower bound for all $N\ge1$. That is false: with $\theta=1$, $\mu=2$, $\gamma=2$ and $N=1$, the endpoint $(m,n)=(0,0)$ satisfies (2.6), because $\Psi_1(1)=\pi^2/6<2$, while $\mathrm{Var}(\log Z_{0,0})=\mathrm{Var}(\log1)=0$. The paper proves the lower bound in Corollary 5.6 "for large enough $N$", and that is what is stated. The constants $C_1,C_2,N_0$ are chosen after $\theta,\mu,\gamma$ and before the probability space (universe `Type`), the environment, $N$, $m$ and $n$. The conclusion also asserts $\log Z_{m,n}\in L^2$, so that the upper bound cannot hold through Mathlib's `variance` junk value $0$. $\gamma$ is an arbitrary real; for $\gamma<0$ condition (2.6) is empty. The paper's remark that the constants can be fixed uniformly for $(\theta,\mu,\gamma)$ in a compact set is not part of the theorem's sentence and is not formalized here.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, Theorem 2.1, p. 6; lower bound for large N: Corollary 5.6, p. 36

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace LogGammaPolymer.Variance

theorem theorem_2_1 {θ μ : ℝ} (hθ : 0 < θ) (hθμ : θ < μ) (γ : ℝ) :
    ∃ C₁ C₂ N₀ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (E : Env θ μ P) (N : ℝ), 1 ≤ N → ∀ m n : ℕ, InRect θ μ γ N m n →
        MemLp (logZ E m n) 2 P ∧
        variance (logZ E m n) P ≤ C₂ * N ^ ((2 : ℝ) / 3) ∧
        (N₀ ≤ N → C₁ * N ^ ((2 : ℝ) / 3) ≤ variance (logZ E m n) P) := by sorry

end LogGammaPolymer.Variance
