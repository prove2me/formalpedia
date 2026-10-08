-- Prove2me | Theorems.Thm_MFGLiquidation_Penalized_theorem_4_6
-- name    : MFGLiquidation.Penalized.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:41.480813+00:00
-- url     : https://prove2.me/theorems/8f72518a-0feb-4524-a394-365a332083db
-- title:
--   Theorem 4.6 — the value functions of the penalized MFGs converge in L¹(Ω) to the value function of the liquidation-constrained MFG
-- statement:
--   Assume Assumption 2.3, let $(A,Z^A)$ be the solution of the singular Riccati BSDE, and assume Assumption 4.1 for $A$.
--
--   **Constrained equilibrium.** Let $(X,Y,Z)\in\mathcal H_\alpha\times L^2_{\mathbb F}([0,T])\times L^2_{\mathbb F}([0,T-])$ solve (2.3) (Theorem 2.4), let $\mu^*_t=\mathbb E[Y_t/(2\eta_t)|\mathcal F^0_t]$ be the equilibrium aggregate rate (2.6), and let $V(\mathcal X)=V(\mathcal X;\mu^*)$ be the value of the constrained problem given $\mu^*$.
--
--   **Penalized equilibria.** Fix $0<\gamma<\alpha\wedge\tfrac12$. For each $n\ge1$ let $A^n$ solve (4.3), let $(X^n,B^n,Y^n,Z^{B^n},Z^{Y^n})$ be the solution of (4.2) in the class of Theorem 4.3, let $\mu^n_t=\mathbb E[Y^n_t/(2\eta_t)|\mathcal F^0_t]$, and let $V^n(\mathcal X)=V^n(\mathcal X;\mu^n)$ be the value of the penalized problem (4.1) given $\mu^n$.
--
--   Then $V^n(\mathcal X)\to V(\mathcal X)$ in $L^1(\Omega)$:
--   $$\lim_{n\to\infty}\mathbb E\big[\,|V^n(\mathcal X)-V(\mathcal X)|\,\big]=0 .$$
--
--   The theorem is a consistency result: the liquidation constraint $X_T=0$, which makes the equilibrium FBSDE singular, is the limit of increasingly heavy penalties $nX_T^2$ on open positions, at the level of equilibrium values.
--
--   **Formalization Note.** The paper names "the" equilibria $\mu^n$ of (4.1) and $\mu^*$ of (1.7). Uniqueness of the penalized equilibrium is not stated in the paper, so both are defined as in the proof (p. 29): through the FBSDE solutions of Theorem 2.4 and Theorem 4.3, as $\mathbb F^0$-progressive versions of $\mathbb E[Y_t/(2\eta_t)|\mathcal F^0_t]$ and $\mathbb E[Y^n_t/(2\eta_t)|\mathcal F^0_t]$. All objects quantified over exist and are unique (Lemma A.1, Theorem 2.4, Lemma A.3, Theorem 4.3), and the conditional essential infima exist, so the statement is neither vacuous nor stronger than printed. The values are conditional essential infima of the costs over the respective admissible sets (constrained: $\int_0^T\xi=\mathcal X$; penalized: all of $L^2_{\mathbb F}$). $L^1$ convergence is $\int|V^n-V|\,d\mathbb P\to0$, computed as a lower integral in $[0,\infty]$; it is not weakened to $\mathbb E[V^n]\to\mathbb E[V]$. Assumption 4.1 is satisfiable, e.g. when $\eta$ is deterministic (Lemma 4.2).
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 29, Theorem 4.6 and the sentence before it; proof pp. 29–30

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MFGLiquidation_Penalized_Setting
import Definitions.Def_MFGLiquidation_Penalized_Game
import Definitions.Def_MFGLiquidation_Penalized_Decoupled
open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Penalized

/-- Theorem 4.6 (p. 29): under Assumptions 2.3 and 4.1, the value functions `Vⁿ(𝒳) = Vⁿ(𝒳; μⁿ)`
of the penalized problems (4.1) at their equilibria converge in `L¹(Ω)` to the value function
`V(𝒳) = V(𝒳; μ*)` of the constrained MFG. -/
theorem theorem_4_6 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Data Ω k} (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) (hRic : IsSingularRiccati hD A ZA)
    (h41 : Assumption41 hD A)
    (X Y : ℝ≥0 → Ω → ℝ) (Z : Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (h23 : SolvesFBSDE23 hD X Y Z) (hX : MemH (filtF hD) P D.T (D.alpha P) X)
    (hY : L2F (filtF hD) P D.T Y) (hZ : IsL2VecMinus (filtF hD) P D.T Z)
    (μ : ℝ≥0 → Ω → ℝ)
    (hμ : IsCondExpVersion (filtF0 hD) P D.T (fun t ω => Y t ω / (2 * D.η t ω)) μ)
    (V : Ω → ℝ) (hV : IsValue hD μ V)
    (γ : ℝ) (hγ : 0 < γ ∧ γ < min (D.alpha P) (1 / 2))
    (An : ℕ → ℝ≥0 → Ω → ℝ) (ZAn : ℕ → Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (hAn : ∀ n : ℕ, 1 ≤ n → IsRegularRiccati hD n (An n) (ZAn n))
    (Xn Bn Yn : ℕ → ℝ≥0 → Ω → ℝ) (ZBn ZYn : ℕ → Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (hsol : ∀ n : ℕ, 1 ≤ n →
      SolvesFBSDE44 hD n (An n) 1 (fun _ _ => 0) (Xn n) (Bn n) (Yn n) (ZBn n) (ZYn n))
    (hclsn : ∀ n : ℕ, 1 ≤ n → ClassFBSDE44 hD n γ (Xn n) (Bn n) (Yn n) (ZBn n) (ZYn n))
    (μn : ℕ → ℝ≥0 → Ω → ℝ)
    (hμn : ∀ n : ℕ, 1 ≤ n →
      IsCondExpVersion (filtF0 hD) P D.T (fun t ω => Yn n t ω / (2 * D.η t ω)) (μn n))
    (Vn : ℕ → Ω → ℝ) (hVn : ∀ n : ℕ, 1 ≤ n → IsValuePen hD n (μn n) (Vn n)) :
    Tendsto (fun n : ℕ => ∫⁻ ω, ‖Vn n ω - V ω‖ₑ ∂P) atTop (𝓝 0) := by sorry

end MFGLiquidation.Penalized
