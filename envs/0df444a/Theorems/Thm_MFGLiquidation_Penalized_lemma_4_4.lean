-- Prove2me | Theorems.Thm_MFGLiquidation_Penalized_lemma_4_4
-- name    : MFGLiquidation.Penalized.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:55.752288+00:00
-- url     : https://prove2.me/theorems/321037ac-2bff-49d5-aae1-7ac30b1565b8
-- title:
--   Lemma 4.4 — ‖Xⁿ‖_{n,α} + ‖Bⁿ‖_{n,γ} + E∫|Yⁿ|² is bounded uniformly in n
-- statement:
--   Assume Assumption 2.3 and fix $\gamma$ with $0<\gamma<\alpha\wedge\tfrac12$. There is a constant $\overline{\mathfrak C}>0$ such that, for every $n\ge1$, the solution $(X^n,B^n,Y^n)$ of (4.2) (that is, (4.4) with $\mathfrak p=1$, $f=0$) in the class of Theorem 4.3 satisfies
--   $$\|X^n\|_{n,\alpha}+\|B^n\|_{n,\gamma}+\mathbb E\Big[\int_0^T|Y^n_t|^2\,dt\Big]\le\overline{\mathfrak C}. \tag{4.5}$$
--
--   The point is uniformity in $n$: the weights $(T-t+\eta_\star/n)^{-l}$ degenerate to the singular weights of $\mathcal H_l$ as $n\to\infty$, and the bound survives the limit. It feeds the convergence of Lemma 4.5.
--
--   **Formalization Note.** $\overline{\mathfrak C}$ is chosen before $n$ and before the solution; it may depend on the data and $\gamma$. The norms are unsquared, as printed, and computed in $[0,\infty]$: $\|U\|_{n,l}$ is the square root of the lower integral defining $\|U\|_{n,l}^2$. The statement quantifies over every solution of (4.3) and every solution of (4.2) in the class; by Lemma A.3 and Theorem 4.3 these are the unique ones.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 26, Lemma 4.4 (4.5)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MFGLiquidation_Penalized_Setting
import Definitions.Def_MFGLiquidation_Penalized_Decoupled
open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Penalized

/-- Lemma 4.4 (p. 26): a bound on `‖Xⁿ‖_{n,α} + ‖Bⁿ‖_{n,γ} + E∫_0^T |Yⁿ_t|² dt` for the solution
of (4.2), uniform in `n`. -/
theorem lemma_4_4 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Data Ω k} (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (γ : ℝ) (hγ : 0 < γ ∧ γ < min (D.alpha P) (1 / 2)) :
    ∃ ℭ : ℝ≥0, 0 < ℭ ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ (An : ℝ≥0 → Ω → ℝ) (ZAn : Fin (k + 1) → ℝ≥0 → Ω → ℝ), IsRegularRiccati hD n An ZAn →
      ∀ (X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
        SolvesFBSDE44 hD n An 1 (fun _ _ => 0) X B Y ZB ZY →
        ClassFBSDE44 hD n γ X B Y ZB ZY →
        hnNormSq D P n (D.alpha P) X ^ (1 / 2 : ℝ) + hnNormSq D P n γ B ^ (1 / 2 : ℝ)
          + ∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) D.T, ‖Y t.toNNReal ω‖ₑ ^ 2 ∂volume ∂P
          ≤ (ℭ : ℝ≥0∞) := by sorry

end MFGLiquidation.Penalized
