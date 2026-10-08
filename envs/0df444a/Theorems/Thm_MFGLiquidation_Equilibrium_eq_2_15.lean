-- Prove2me | Theorems.Thm_MFGLiquidation_Equilibrium_eq_2_15
-- name    : MFGLiquidation.Equilibrium.eq_2_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:27.293034+00:00
-- url     : https://prove2.me/theorems/23ddc8f2-52ce-4986-86ae-7eaf1e0d3dca
-- title:
--   (2.15) — 𝔼[X^ξ_s Y_s | 𝒳] → 0 as s ↗ T for every admissible ξ
-- statement:
--   Assume Assumption 2.3, let $(A,Z^A)$ solve the singular Riccati BSDE, $0<\gamma<\alpha\wedge\frac12$, and let $(X,B,Y,Z^B,Z^Y)$ be a solution of (2.3) and (2.10) in the class of Proposition 2.8. Let $\xi\in\mathcal A_{\mathbb F}(\mathcal X)$ and $X^\xi_t=\mathcal X-\int_0^t\xi_sds$. Then for every sequence $s_n<T$ with $s_n\to T$,
--   $$\lim_{n\to\infty}\mathbb E\big[X^\xi_{s_n}Y_{s_n}\ \big|\ \mathcal X\big]=0\quad\text{a.s.}$$
--   This limit removes the boundary term at the singular time in the verification argument for the optimality of $\xi^*$.
--
--   **Formalization Note** The paper writes $\lim_{s\nearrow T}$ without a mode of convergence; it is stated a.s. along every sequence in $[0,T)$ converging to $T$, which is the form a conditional dominated convergence argument gives. The solution of Proposition 2.8 is a hypothesis.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 15, proof of Proposition 2.9, (2.15)

import Mathlib
import Definitions.Def_MFGLiquidation_Equilibrium_Setting
import Definitions.Def_MFGLiquidation_Equilibrium_Decoupled
import Definitions.Def_MFGLiquidation_Equilibrium_Game

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLiquidation.Equilibrium

open Peng1990.SMP

theorem eq_2_15 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (D : Data Ω k) (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) (hR : IsSingularRiccati hD A ZA)
    (γ : ℝ) (hγ0 : 0 < γ) (hγα : γ < D.alpha P) (hγ2 : γ < 1 / 2)
    (X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (hcl : ClassFBSDE211 hD γ X B Y ZB ZY) (h210 : SolvesFBSDE211 hD A 1 0 X B Y ZB ZY)
    (h23 : SolvesFBSDE23 hD X Y ZY)
    (ξ : ℝ≥0 → Ω → ℝ) (hξ : IsAdmissible hD ξ) :
    ∀ s : ℕ → ℝ≥0, (∀ n, s n < D.T) → Tendsto s atTop (𝓝 D.T) →
      ∀ᵐ ω ∂P, Tendsto (fun n => (P[fun ω' => stateOf D ξ (s n) ω' * Y (s n) ω' |
        MeasurableSpace.comap D.𝒳 inferInstance]) ω) atTop (𝓝 0) := by sorry

end MFGLiquidation.Equilibrium
