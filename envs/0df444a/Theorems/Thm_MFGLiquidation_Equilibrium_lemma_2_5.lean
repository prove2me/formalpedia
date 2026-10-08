-- Prove2me | Theorems.Thm_MFGLiquidation_Equilibrium_lemma_2_5
-- name    : MFGLiquidation.Equilibrium.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:55.883057+00:00
-- url     : https://prove2.me/theorems/2a3f6ec1-bf7e-4034-aec5-0867cd88c5de
-- title:
--   Lemma 2.5 — a priori L² estimate for Z^B and Z^Y in the decoupled FBSDE (2.11)
-- statement:
--   Assume Assumption 2.3, let $(A,Z^A)$ solve the singular Riccati BSDE, let $0<\gamma<\alpha\wedge\frac12$ and $\mathfrak p\in[0,1]$. There is a constant $C>0$ such that the following holds for every $f\in L^2_{\mathbb F}([0,T]\times\Omega;\mathbb R)$ and every solution $(X,B,Y,Z^B,Z^Y)$ of (2.11) with $(X,B,Y)\in\mathcal H_\alpha\times\mathcal H_\gamma\times S^2_{\mathbb F}([0,T-]\times\Omega;\mathbb R)$:
--
--   1. $(Z^B,Z^Y)\in L^2_{\mathbb F}([0,T]\times\Omega;\mathbb R^m)\times L^2_{\mathbb F}([0,T-]\times\Omega;\mathbb R^m)$;
--   2. $$\mathbb E\Big[\int_0^T|Z^B_t|^2dt\Big]\le C\Big(\|B\|_\gamma^2+\|X\|_\alpha^2+\mathbb E\Big[\int_0^T|f_t|^2dt\Big]\Big);$$
--   3. for each $\tau<T$, $$\mathbb E\Big[\int_0^\tau|Z^Y_s|^2ds\Big]\le C\Big(\mathbb E\Big[\sup_{0\le t\le\tau}|Y_t|^2\Big]+\|X\|_\alpha^2+\|B\|_\gamma^2+\mathbb E\Big[\int_0^T|f_t|^2dt\Big]\Big);$$
--   4. $\int_0^\cdot Z^B_s\,d\widetilde W_s$ exists and is a true martingale on $[0,T]$, and $\int_0^\cdot Z^Y_s\,d\widetilde W_s$ exists and is a true martingale on $[0,\tau]$ for each $\tau<T$.
--
--   The lemma upgrades the local square integrability of the martingale parts, which is all the equation gives near the singular time $T$, to global estimates; it is the a priori bound behind the contraction in Lemma 2.7.
--
--   **Formalization Note** The constant comes after $\mathfrak p$, $\gamma$, the data and $A$, and before $f$ and the solution: it may depend on the coefficients, $T$, $A$, $\gamma$ and $\mathfrak p$, never on $f$ or the solution. $|Z|^2=\sum_j|Z^j|^2$. The integrals are lower Lebesgue integrals in $[0,\infty]$, and $\|\cdot\|_\gamma^2$ is the squared $\mathcal H_\gamma$ norm. "True martingale" is stated for every vector of Itô integral processes of the integrand (each is determined up to a.s. equality at every $t$), together with the existence of one, as integrability at each $t$ and $\mathbb E[M_t\mid\mathcal F_s]=M_s$ for $s\le t$ in the interval. Assumption 2.3 is the paper's standing assumption of §§2–4 (p. 8).
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 10, Lemma 2.5

import Mathlib
import Definitions.Def_MFGLiquidation_Equilibrium_Setting
import Definitions.Def_MFGLiquidation_Equilibrium_Decoupled

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLiquidation.Equilibrium

open Peng1990.SMP

theorem lemma_2_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (D : Data Ω k) (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) (hR : IsSingularRiccati hD A ZA)
    (γ : ℝ) (hγ0 : 0 < γ) (hγα : γ < D.alpha P) (hγ2 : γ < 1 / 2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
        L2F (filtF hD) P D.T f → SolvesFBSDE211 hD A p f X B Y ZB ZY →
        MemH (filtF hD) P D.T (D.alpha P) X → MemH (filtF hD) P D.T γ B →
        IsS2Minus (filtF hD) P D.T Y →
        IsL2Vec (filtF hD) P D.T ZB ∧ IsL2VecMinus (filtF hD) P D.T ZY ∧
        (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) D.T, ∑ j, ‖ZB j s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P) ≤
          ENNReal.ofReal C * (hNormSq D.T P γ B + hNormSq D.T P (D.alpha P) X +
            ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) D.T, ‖f s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P) ∧
        (∀ τ < D.T,
          (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) τ, ∑ j, ‖ZY j s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P) ≤
            ENNReal.ofReal C * ((∫⁻ ω, ⨆ t ∈ Set.Iic τ, ‖Y t ω‖ₑ ^ 2 ∂P) +
              hNormSq D.T P (D.alpha P) X + hNormSq D.T P γ B +
              ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) D.T, ‖f s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P)) ∧
        (∃ J : Fin (k + 1) → ℝ≥0 → Ω → ℝ, IsItoIntegralVec (filtF hD) P D.T D.W ZB J) ∧
        (∀ J : Fin (k + 1) → ℝ≥0 → Ω → ℝ, IsItoIntegralVec (filtF hD) P D.T D.W ZB J →
          IsMartingaleOn (filtF hD) P D.T (fun t ω => ∑ j, J j t ω)) ∧
        ∀ τ < D.T,
          (∃ J : Fin (k + 1) → ℝ≥0 → Ω → ℝ, IsItoIntegralVec (filtF hD) P τ D.W ZY J) ∧
          ∀ J : Fin (k + 1) → ℝ≥0 → Ω → ℝ, IsItoIntegralVec (filtF hD) P τ D.W ZY J →
            IsMartingaleOn (filtF hD) P τ (fun t ω => ∑ j, J j t ω) := by sorry

end MFGLiquidation.Equilibrium
