-- Prove2me | Theorems.Thm_MFGLiquidation_Equilibrium_proposition_2_8
-- name    : MFGLiquidation.Equilibrium.proposition_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:41.202378+00:00
-- url     : https://prove2.me/theorems/88cdd3a7-85a9-4687-b1df-530c2d489bdb
-- title:
--   Proposition 2.8 — the FBSDEs (2.3) and (2.10) have a unique joint solution, bounded in terms of η, λ, κ, T and ‖𝒳‖_{L²}
-- statement:
--   Assume Assumption 2.3, let $(A,Z^A)$ solve the singular Riccati BSDE and let $0<\gamma<\alpha\wedge\frac12$.
--
--   1. There is $(X,B,Y,Z^B,Z^Y)\in\mathcal H_\alpha\times\mathcal H_\gamma\times D^2_{\mathbb F}([0,T]\times\Omega;\mathbb R)\times L^2_{\mathbb F}([0,T]\times\Omega;\mathbb R^m)\times L^2_{\mathbb F}([0,T-]\times\Omega;\mathbb R^m)$ such that $(X,Y,Z^Y)$ solves the FBSDE (2.3), $(X,B,Z^B)$ solves (2.10) (that is, (2.11) with $\mathfrak p=1$, $f=0$) and $Y=AX+B$ on $[0,T)$.
--   2. Any two such solutions agree.
--   3. For every $R\ge0$ there is $C>0$ such that, for every initial portfolio $\mathcal X'$ on the same probability space with $\|\mathcal X'\|_{L^2}\le R$ for which the data $(\mathcal X',\widetilde W,\kappa,\lambda,\eta,T)$ satisfy the standing structure and Assumption 2.3, every such solution for $\mathcal X'$ (with the corresponding Riccati solution) satisfies
--   $$\|X\|_{\mathcal H_\alpha}+\|B\|_{\mathcal H_\gamma}+\mathbb E\Big[\int_0^T|Y_t|^2dt\Big]\le C.$$
--
--   This proposition is the end point of the method of continuation and the source of the equilibrium candidate $\xi^*=Y/(2\eta)$.
--
--   **Formalization Note** "A constant $C>0$ depending on $\eta,\lambda,\kappa,T$ and $\|\mathcal X\|_{L^2}$": a constant chosen after the whole data would only restate finiteness, which the solution class already contains. The statement fixes the probability space, $\widetilde W$, $T$ and the coefficient processes, and asks $C$ to be uniform over initial portfolios in an $L^2$ ball; the filtration $\mathbb F$ depends on $\mathcal X'$, so Assumption 2.3 and the Riccati solution are taken relative to each $\mathcal X'$. Since $\alpha$ depends only on $\eta$, the classes for $\mathcal X'$ and $\mathcal X$ use the same $\alpha$. Including the third equation of (2.11) is harmless: given $Y=AX+B$, it is equivalent to the backward equation of (2.3).
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 15, Proposition 2.8

import Mathlib
import Definitions.Def_MFGLiquidation_Equilibrium_Setting
import Definitions.Def_MFGLiquidation_Equilibrium_Decoupled

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLiquidation.Equilibrium

open Peng1990.SMP

theorem proposition_2_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (D : Data Ω k) (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) (hR : IsSingularRiccati hD A ZA)
    (γ : ℝ) (hγ0 : 0 < γ) (hγα : γ < D.alpha P) (hγ2 : γ < 1 / 2) :
    (∃ (X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
      ClassFBSDE211 hD γ X B Y ZB ZY ∧ SolvesFBSDE211 hD A 1 0 X B Y ZB ZY ∧
      SolvesFBSDE23 hD X Y ZY) ∧
    (∀ (X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ)
      (X' B' Y' : ℝ≥0 → Ω → ℝ) (ZB' ZY' : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
      ClassFBSDE211 hD γ X B Y ZB ZY → SolvesFBSDE211 hD A 1 0 X B Y ZB ZY →
      SolvesFBSDE23 hD X Y ZY →
      ClassFBSDE211 hD γ X' B' Y' ZB' ZY' → SolvesFBSDE211 hD A 1 0 X' B' Y' ZB' ZY' →
      SolvesFBSDE23 hD X' Y' ZY' →
      AgreeFBSDE211 hD X B Y ZB ZY X' B' Y' ZB' ZY') ∧
    ∀ R : ℝ, ∃ C : ℝ, 0 < C ∧
      ∀ (D' : Data Ω k), D'.T = D.T → D'.W = D.W → D'.κ = D.κ → D'.lam = D.lam → D'.η = D.η →
      ∀ (hD' : D'.Standing P), D'.Assumption23 P hD' → eLpNorm D'.𝒳 2 P ≤ ENNReal.ofReal R →
      ∀ (A' : ℝ≥0 → Ω → ℝ) (ZA' : Fin (k + 1) → ℝ≥0 → Ω → ℝ), IsSingularRiccati hD' A' ZA' →
      ∀ (X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
        ClassFBSDE211 hD' γ X B Y ZB ZY → SolvesFBSDE211 hD' A' 1 0 X B Y ZB ZY →
        SolvesFBSDE23 hD' X Y ZY →
        Real.sqrt (hNormSq D.T P (D.alpha P) X).toReal + Real.sqrt (hNormSq D.T P γ B).toReal +
          (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) D.T, ‖Y s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P).toReal ≤ C := by sorry

end MFGLiquidation.Equilibrium
