-- Prove2me | Theorems.Thm_MFGLiquidation_Penalized_theorem_4_3
-- name    : MFGLiquidation.Penalized.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:25.363294+00:00
-- url     : https://prove2.me/theorems/93852568-d355-4e74-bc5a-009bf0829b46
-- title:
--   Theorem 4.3 — the penalized conditional mean-field FBSDE (4.4) has a unique solution in ℋⁿ_α × ℋⁿ_γ × S² × L² × L²
-- statement:
--   Assume Assumption 2.3 (which includes $\mathcal X\in L^2$). Fix $n\ge1$, the solution $(A^n,Z^{A^n})$ of (4.3), a constant $\gamma$ with $0<\gamma<\alpha\wedge\tfrac12$, a parameter $\mathfrak p\in[0,1]$ and $f\in L^2_{\mathbb F}([0,T]\times\Omega;\mathbb R)$. Then the FBSDE
--   $$\begin{aligned}dX^n_t&=-\tfrac{1}{2\eta_t}(A^n_tX^n_t+B^n_t)\,dt,\\ -dB^n_t&=\Big(\kappa_t\mathfrak p\,\mathbb E\Big[\tfrac{1}{2\eta_t}(A^n_tX^n_t+B^n_t)\Big|\mathcal F^0_t\Big]+f_t-\tfrac{A^n_tB^n_t}{2\eta_t}\Big)dt-Z^{B^n}_t\,d\widetilde W_t,\\ dY^n_t&=\Big(-2\lambda_tX^n_t-\kappa_t\mathfrak p\,\mathbb E\Big[\tfrac{A^n_tX^n_t+B^n_t}{2\eta_t}\Big|\mathcal F^0_t\Big]-f_t\Big)dt+Z^{Y^n}_t\,d\widetilde W_t,\\ X^n_0&=\mathcal X,\quad B^n_T=0,\quad Y^n_T=2nX^n_T\end{aligned}\tag{4.4}$$
--   has a solution
--   $$(X^n,B^n,Y^n,Z^{B^n},Z^{Y^n})\in\mathcal H^n_\alpha\times\mathcal H^n_\gamma\times S^2_{\mathbb F}([0,T])\times L^2_{\mathbb F}([0,T];\mathbb R^m)\times L^2_{\mathbb F}([0,T];\mathbb R^m),$$
--   and any two solutions in this class agree: $X^n,B^n,Y^n$ almost surely at every $t\le T$, and $Z^{B^n},Z^{Y^n}$ $dt\otimes d\mathbb P$-a.e.
--
--   With $\mathfrak p=1$, $f=0$ this is the solvability of (4.2), the FBSDE characterizing the equilibrium of the penalized MFG; the general $\mathfrak p$ is what a continuation argument requires.
--
--   **Formalization Note.** "$\mathcal X$ is a square integrable random variable" is part of Assumption 2.3(i) and is not repeated. $\gamma$ is the constant of p. 9 ("any constant $0<\gamma<\alpha\wedge1/2$"), a binder with that hypothesis. The conditional expectation is evaluated through one $\mathbb F^0$-progressive version, used in both equations.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 26, Theorem 4.3 (4.4); γ from p. 9

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MFGLiquidation_Penalized_Setting
import Definitions.Def_MFGLiquidation_Penalized_Decoupled
open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Penalized

/-- Theorem 4.3 (p. 26): for every `n ≥ 1`, `𝔭 ∈ [0, 1]` and `f ∈ L²_𝔽`, the penalized FBSDE (4.4)
has a solution in `ℋⁿ_α × ℋⁿ_γ × S² × L² × L²`, and any two solutions in that class agree. -/
theorem theorem_4_3 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Data Ω k} (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (γ : ℝ) (hγ : 0 < γ ∧ γ < min (D.alpha P) (1 / 2))
    (n : ℕ) (hn : 1 ≤ n) (An : ℝ≥0 → Ω → ℝ) (ZAn : Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (hAn : IsRegularRiccati hD n An ZAn)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (f : ℝ≥0 → Ω → ℝ) (hf : L2F (filtF hD) P D.T f) :
    (∃ (X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
      SolvesFBSDE44 hD n An p f X B Y ZB ZY ∧ ClassFBSDE44 hD n γ X B Y ZB ZY) ∧
    ∀ (X B Y X' B' Y' : ℝ≥0 → Ω → ℝ) (ZB ZY ZB' ZY' : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
      SolvesFBSDE44 hD n An p f X B Y ZB ZY → ClassFBSDE44 hD n γ X B Y ZB ZY →
      SolvesFBSDE44 hD n An p f X' B' Y' ZB' ZY' → ClassFBSDE44 hD n γ X' B' Y' ZB' ZY' →
      (∀ t ≤ D.T, X t =ᵐ[P] X' t ∧ B t =ᵐ[P] B' t ∧ Y t =ᵐ[P] Y' t) ∧
        ∀ j, ∀ᵐ q ∂(dtP D.T P),
          ZB j q.1.toNNReal q.2 = ZB' j q.1.toNNReal q.2 ∧
            ZY j q.1.toNNReal q.2 = ZY' j q.1.toNNReal q.2 := by sorry

end MFGLiquidation.Penalized
