-- Prove2me | Theorems.Thm_MFGLiquidation_Penalized_lemma_4_5
-- name    : MFGLiquidation.Penalized.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:52.632367+00:00
-- url     : https://prove2.me/theorems/c37b5d31-cba5-41e1-84ec-eefa73344a87
-- title:
--   Lemma 4.5 — the penalized solutions (Xⁿ, Bⁿ, Yⁿ) converge in L²(dt ⊗ dP) to the constrained solution (X, B, Y)
-- statement:
--   Assume Assumptions 2.3 and 4.1. Let $(X,B,Y)$ be the solution of the FBSDEs (2.3) and (2.10) given by Proposition 2.8 (as in (4.8), with some $0<\gamma<\alpha\wedge\tfrac12$), and for each $n\ge1$ let $(X^n,B^n,Y^n)$ be the solution of (4.2) in the class of Theorem 4.3 (same $\gamma$), built on the solution $A^n$ of (4.3). Then
--   $$\lim_{n\to+\infty}\Big\{\mathbb E\Big[\int_0^T|X^n_t-X_t|^2dt\Big]+\mathbb E\Big[\int_0^T|B^n_t-B_t|^2dt\Big]+\mathbb E\Big[\int_0^T|Y^n_t-Y_t|^2dt\Big]\Big\}=0.$$
--
--   This is the convergence of the optimal positions and controls ($\xi^{n,*}=Y^n/(2\eta)$, $\xi^*=Y/(2\eta)$) on which the convergence of the values in Theorem 4.6 rests.
--
--   **Formalization Note.** The expectations are lower integrals in $[0,\infty]$. The solutions are hypotheses, indexed by $n\in\mathbb N$ with hypotheses for $n\ge1$; the values at $n=0$ are irrelevant to the limit. The relation $Y=AX+B$ on $[0,T)$ is part of the solution concept of Proposition 2.8.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 28, Lemma 4.5

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MFGLiquidation_Penalized_Setting
import Definitions.Def_MFGLiquidation_Penalized_Decoupled
open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Penalized

/-- Lemma 4.5 (p. 28): under Assumptions 2.3 and 4.1 the solutions `(Xⁿ, Bⁿ, Yⁿ)` of (4.2)
converge in `L²(dt ⊗ dP)` to the solution `(X, B, Y)` of (2.3) and (2.10). -/
theorem lemma_4_5 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Data Ω k} (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) (hRic : IsSingularRiccati hD A ZA)
    (h41 : Assumption41 hD A) (γ : ℝ) (hγ : 0 < γ ∧ γ < min (D.alpha P) (1 / 2))
    (X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (h23 : SolvesFBSDE23 hD X Y ZY) (h210 : SolvesFBSDE210 hD A X B ZB)
    (hrel : ∀ t < D.T, Y t =ᵐ[P] fun ω => A t ω * X t ω + B t ω)
    (hcls : ClassFBSDE211 hD γ X B Y ZB ZY)
    (An : ℕ → ℝ≥0 → Ω → ℝ) (ZAn : ℕ → Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (hAn : ∀ n : ℕ, 1 ≤ n → IsRegularRiccati hD n (An n) (ZAn n))
    (Xn Bn Yn : ℕ → ℝ≥0 → Ω → ℝ) (ZBn ZYn : ℕ → Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (hsol : ∀ n : ℕ, 1 ≤ n →
      SolvesFBSDE44 hD n (An n) 1 (fun _ _ => 0) (Xn n) (Bn n) (Yn n) (ZBn n) (ZYn n))
    (hclsn : ∀ n : ℕ, 1 ≤ n → ClassFBSDE44 hD n γ (Xn n) (Bn n) (Yn n) (ZBn n) (ZYn n)) :
    Tendsto (fun n : ℕ =>
        ∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) D.T, ‖Xn n t.toNNReal ω - X t.toNNReal ω‖ₑ ^ 2 ∂volume ∂P
        + ∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) D.T, ‖Bn n t.toNNReal ω - B t.toNNReal ω‖ₑ ^ 2 ∂volume ∂P
        + ∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) D.T, ‖Yn n t.toNNReal ω - Y t.toNNReal ω‖ₑ ^ 2 ∂volume ∂P)
      atTop (𝓝 0) := by sorry

end MFGLiquidation.Penalized
