-- Prove2me | Theorems.Thm_GloriaOtto_Variance_theorem_2_1
-- name    : GloriaOtto.Variance.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:31.814983+00:00
-- url     : https://prove2.me/theorems/a65d10f2-c975-46a7-9929-3ba3dcc28cc7
-- title:
--   Theorem 2.1 — var[ξ·A_{L,T}ξ] ≲ L^{−d} for d > 2 and ≲ L^{−2}(ln T)^q for d = 2
-- statement:
--   Let $d \ge 2$, $0 < \alpha \le \beta$, and let the conductivities be i.i.d. with a law $\nu$ supported in $[\alpha,\beta]$. For $\xi \in \mathbb R^d$ with $|\xi| = 1$, $T > 0$ and a mask $\eta_L$ as in (3.15), define the averaged energy density of the approximate corrector
--   $$\xi\cdot A_{L,T}\xi := \sum_{x\in\mathbb Z^d}\Big(T^{-1}\phi_T(x)^2 + \big(\nabla\phi_T(x)+\xi\big)\cdot A(x)\big(\nabla\phi_T(x)+\xi\big)\Big)\eta_L(x).$$
--
--   Then there exist an exponent $q > 0$ and a threshold $T_0 \ge e$, depending only on $d, \alpha, \beta$, and for every mask constant $C_\eta$ a constant $C$ depending only on $d, \alpha, \beta, C_\eta$, such that for every such law $\nu$, every unit $\xi$, every $T \ge T_0$, every $L > 0$ and every mask $\eta_L$ with constant $C_\eta$: the random variable $\xi\cdot A_{L,T}\xi$ is square-integrable and
--   $$\operatorname{var}[\xi\cdot A_{L,T}\xi] \le \begin{cases} C L^{-2}(\ln T)^q, & d = 2,\\ C L^{-d}, & d > 2.\end{cases} \tag{2.5}$$
--
--   Spatial averages of the energy density thus fluctuate at the rate $L^{-d/2}$ of an average of independent variables, up to a logarithm in $d=2$. This is the variance estimate used in the error analysis of approximations of the homogenized coefficients.
--
--   **Formalization Note.** "$T \gg 1$" is $T \ge T_0$ with $T_0 \ge e$, so $\ln T \ge 1$. The constants $q, T_0, C$ are chosen before the law $\nu$, $\xi$, $T$, $L$ and $\eta_L$, which is the paper's convention that $\lesssim$ depends only on $d, \alpha, \beta$ (and here on the mask constant). The paper says $q$ depends only on $\alpha, \beta$; here it is chosen after $d$, as on p. 28 ("depending only on $\alpha, \beta$, and $d$"), which matters only at $d = 2$. Square-integrability is part of the conclusion, so the variance cannot vanish by a non-integrability default. The mask is the paper's (3.15), including $0 \le \eta_L \le 1$. The last sentence of the theorem (the corrector $\phi$ itself for $d > 2$) is not formalized.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, Theorem 2.1, (2.5), p. 11; mask (3.15), p. 28

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem theorem_2_1 (d : ℕ) (hd : 2 ≤ d) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ q : ℝ, 0 < q ∧ ∃ T₀ : ℝ, Real.exp 1 ≤ T₀ ∧ ∀ Cη : ℝ, ∃ C : ℝ,
      ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], ν (Set.Icc α β)ᶜ = 0 →
      ∀ ξ : Fin d → ℝ, sqNorm ξ = 1 → ∀ T : ℝ, T₀ ≤ T → ∀ L : ℝ, 0 < L →
      ∀ η : Site d → ℝ, IsMask L Cη η →
        MemLp (fun a => energyAvg a T ξ η) 2 (law d ν) ∧
        variance (fun a => energyAvg a T ξ η) (law d ν)
          ≤ C * L ^ (-(d : ℝ)) * (if d = 2 then Real.log T ^ q else 1) := by sorry

end GloriaOtto.Variance
