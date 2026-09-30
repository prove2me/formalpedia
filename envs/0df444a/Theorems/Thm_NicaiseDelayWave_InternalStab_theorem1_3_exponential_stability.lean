-- Prove2me | Theorems.Thm_NicaiseDelayWave_InternalStab_theorem1_3_exponential_stability
-- name    : NicaiseDelayWave.InternalStab.theorem1_3_exponential_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T20:32:54.824717+00:00
-- url     : https://prove2.me/theorems/b68846e9-cbad-401d-9e87-5cce4953f34c
-- title:
--   Theorem 1.3 — exponential decay 𝓕(t) ≤ C1𝓕(0)e^{−C2t} under delayed internal damping when μ2 < μ1
-- statement:
--   Let $\Omega\subset\mathbb{R}^n$ ($n\ge1$) be a bounded open set with $C^2$ boundary $\Gamma=\Gamma_D\cup\Gamma_N$, $\overline{\Gamma_D}\cap\overline{\Gamma_N}=\emptyset$, $\Gamma_D\ne\emptyset$, outer normal $\nu$. Assume:
--
--   1. there are $v\in C^2$ and $\alpha>0$ with $\langle D^2v(x)\xi,\xi\rangle\ge2\alpha|\xi|^2$ on $\overline\Omega$ and $\nabla v\cdot\nu\le0$ on $\Gamma_D$ (1.6)–(1.7);
--   2. $\omega\subset\Omega$ is an open neighbourhood of $\Gamma_N$ in $\Omega$, and $a\in L^\infty(\Omega)$ satisfies $a\ge0$ a.e. in $\Omega$ (1.17) and $a>a_0>0$ a.e. in $\omega$ (1.18);
--   3. $\mu_1,\mu_2,\tau>0$ with $\mu_2<\mu_1$ (1.8), and $\tau\mu_2<\xi<\tau(2\mu_1-\mu_2)$ (1.10).
--
--   Then there exist positive constants $C_1,C_2$ such that for every regular solution $u$ of
--   $$u_{tt}-\Delta u+a(x)\big[\mu_1u_t(x,t)+\mu_2u_t(x,t-\tau)\big]=0\ \text{in }\Omega\times(0,\infty),\quad u=0\ \text{on }\Gamma_D,\quad \frac{\partial u}{\partial\nu}=0\ \text{on }\Gamma_N,$$
--   the energy
--   $$\mathcal{F}(t)=\frac12\int_\Omega\{u_t^2+|\nabla u|^2\}dx+\frac\xi2\int_\Omega a(x)\int_0^1u_t^2(x,t-\tau\rho)\,d\rho\,dx$$
--   satisfies
--   $$\mathcal{F}(t)\le C_1\,\mathcal{F}(0)\,e^{-C_2t}\qquad\forall t\ge0 .$$
--
--   The constants depend on the domain, $v$, $\alpha$, $\omega$, $a$, $a_0$, $\mu_1,\mu_2,\tau,\xi$ but not on the solution. The theorem shows that a delayed internal feedback does not destroy exponential stability as long as the delayed gain $\mu_2$ is dominated by the undelayed gain $\mu_1$.
--
--   **Formalization Note** Solutions are classical: $u\in C^2(\mathbb{R}^n\times\mathbb{R})$, with the equation imposed for a.e. $x\in\Omega$ at each $t>0$ (since $a$ is only $L^\infty$) and the initial data and history given by the values of $u$ at $t\le0$; this is a subclass of the paper's solutions. The hypothesis that the closure of every connected component of $\Omega$ meets $\Gamma_D$ (true whenever $\Omega$ is connected) is added: the proof's Poincaré inequality and its compactness–uniqueness step need it.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1563, Theorem 1.3 (1.20)

import Mathlib
import Definitions.Def_NicaiseDelayWave_InternalStab_InternalDampingProblem

namespace NicaiseDelayWave.InternalStab

open MeasureTheory

theorem theorem1_3_exponential_stability {n : ℕ} (hn : 1 ≤ n) (D : NicaiseDelayWave.Shared.MixedDomain n)
    (hcomp : ∀ x ∈ D.Ω, (closure (connectedComponentIn D.Ω x) ∩ D.ΓD).Nonempty)
    (v : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ) (hv : ConvexMultiplier D v α)
    (ω : Set (EuclideanSpace ℝ (Fin n))) (hω : IsInteriorNbhdΓN D ω)
    (a : EuclideanSpace ℝ (Fin n) → ℝ) (ha : IsDampingCoefficient D a)
    (a0 : ℝ) (ha0 : 0 < a0) (haω : ∀ᵐ x ∂(volume.restrict ω), a0 < a x)
    (μ1 μ2 τ ξ : ℝ) (hμ1 : 0 < μ1) (hμ2 : 0 < μ2) (hτ : 0 < τ) (h18 : μ2 < μ1)
    (h110 : τ * μ2 < ξ ∧ ξ < τ * (2 * μ1 - μ2)) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      ∀ u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ, IsRegularSolution D a μ1 μ2 τ u →
        ∀ t ≥ 0, energyF D a ξ τ u t ≤ C1 * energyF D a ξ τ u 0 * Real.exp (-C2 * t) := by sorry

end NicaiseDelayWave.InternalStab
