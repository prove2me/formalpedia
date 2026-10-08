-- Prove2me | Theorems.Thm_MFGLiquidation_Penalized_eq_4_8
-- name    : MFGLiquidation.Penalized.eq_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:46.524825+00:00
-- url     : https://prove2.me/theorems/040a8c4e-bc24-4b32-8ccf-8d710c271233
-- title:
--   (4.8) — under Assumption 4.1 the equilibrium portfolio satisfies ‖X*‖₁ < ∞
-- statement:
--   Assume Assumption 2.3, let $(A,Z^A)$ be the singular Riccati solution, and assume Assumption 4.1 for $A$. Let $(X,B,Y,Z^B,Z^Y)$ be the solution of Proposition 2.8: $(X,Y,Z^Y)$ solves (2.3), $(X,B,Z^B)$ solves (2.10), $Y=AX+B$ on $[0,T)$, and $(X,B,Y,Z^B,Z^Y)\in\mathcal H_\alpha\times\mathcal H_\gamma\times D^2\times L^2\times L^2([0,T-])$ for some $0<\gamma<\alpha\wedge\tfrac12$. Then $X=X^*\in\mathcal H_1$, i.e.
--   $$\|X^*\|_1=\Big(\mathbb E\Big[\sup_{0\le t\le T}\Big|\frac{X_t}{T-t}\Big|^2\Big]\Big)^{1/2}<\infty. \tag{4.8}$$
--
--   Without Assumption 4.1 only $X\in\mathcal H_\alpha$ with $\alpha=\eta_\star/\|\eta\|\le1$ is known; the improvement to $\alpha=1$ is what makes the error terms of Lemma 4.5 vanish.
--
--   **Formalization Note.** The paper prints "the estimate of Theorem 2.8"; this means Proposition 2.8. The solution of Proposition 2.8 is taken as a hypothesis (it exists and is unique by Proposition 2.8); the relation $Y=AX+B$ is part of its solution concept (without it (2.11) would not be uniquely solvable).
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 28, (4.8)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MFGLiquidation_Penalized_Setting
import Definitions.Def_MFGLiquidation_Penalized_Decoupled
open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Penalized

/-- (4.8) (p. 28): under Assumption 4.1, the state component `X` of the solution of (2.3) and
(2.10) given by Proposition 2.8 lies in `ℋ_1`, i.e. `‖X*‖_1 < ∞`. -/
theorem eq_4_8 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Data Ω k} (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) (hRic : IsSingularRiccati hD A ZA)
    (h41 : Assumption41 hD A) (γ : ℝ) (hγ : 0 < γ ∧ γ < min (D.alpha P) (1 / 2))
    (X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (h23 : SolvesFBSDE23 hD X Y ZY) (h210 : SolvesFBSDE210 hD A X B ZB)
    (hrel : ∀ t < D.T, Y t =ᵐ[P] fun ω => A t ω * X t ω + B t ω)
    (hcls : ClassFBSDE211 hD γ X B Y ZB ZY) :
    MemH (filtF hD) P D.T 1 X := by sorry

end MFGLiquidation.Penalized
