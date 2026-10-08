-- Prove2me | Theorems.Thm_KPZ2D_Polymer_theorem_1_6
-- name    : KPZ2D.Polymer.theorem_1_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:54.312987+00:00
-- url     : https://prove2.me/theorems/e3742b0f-1283-4128-b851-28ea3795eab9
-- title:
--   Theorem 1.6, p. 6 — Edwards–Wilkinson fluctuations of the two-dimensional directed polymer
-- statement:
--   Let $Z_{N,\beta_N}(x)$ be the two-dimensional directed-polymer partition function (1.22), where $\beta_N=\hat\beta/\sqrt{R_N}$, $\hat\beta\in(0,1)$, and the i.i.d. disorder satisfies (1.19)–(1.20). For $t>0$ set
--
--   $$\mathfrak h_N(t,y)=\frac{\log Z_{\lfloor tN\rfloor}(\lfloor\sqrt N y\rfloor)-\mathbb E[\log Z_{\lfloor tN\rfloor}(0)]}{\beta_N}.\tag{1.23}$$
--
--   For every smooth compactly supported $\phi:\mathbb R^2\to\mathbb R$,
--
--   $$\int_{\mathbb R^2}\mathfrak h_N(t,y)\phi(y)\,dy\xrightarrow{d}\langle v^{(\sqrt2c_{\hat\beta})}(t/2,\cdot),\phi\rangle,\qquad c_{\hat\beta}=\sqrt{\frac1{1-\hat\beta^2}}.\tag{1.24}$$
--
--   The limit is centred Gaussian with variance $(\sqrt2c_{\hat\beta})^2\sigma_\phi^2(t/2)$ and covariance kernel (1.14). This is the paper's Edwards–Wilkinson fluctuation result for the polymer throughout the subcritical interval.
--
--   **Formalization Note** The tested additive stochastic heat field is represented through its Gaussian law. The function class is $C_c^\infty$, not the analytic compact-support class. The numerator uses the partition function at $\lfloor tN\rfloor$ and its corresponding $\beta_{\lfloor tN\rfloor}$; the denominator is $\beta_N$, as printed.
-- source:
--   Caravenna, Sun, Zygouras, The two-dimensional KPZ equation in the entire subcritical regime, arXiv:1812.03911v3, Theorem 1.6, (1.23)–(1.24), p. 6

import Mathlib
import Definitions.Def_PolymerEndpoint_Atomic_Model
import Definitions.Def_KPZ2D_Polymer_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology ContDiff

namespace KPZ2D.Polymer

/-- Edwards–Wilkinson fluctuations of the two-dimensional directed polymer, Theorem 1.6. -/
theorem theorem_1_6 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (h119 : Assumption119 𝔏) (γ C₁ C₂ : ℝ)
    (h120 : Concentration120 𝔏 γ C₁ C₂)
    (env : PolymerEndpoint.Atomic.Cell 2 → Ω → ℝ)
    (henv : PolymerEndpoint.Atomic.IsEnvironment env 𝔏 P)
    (βhat : ℝ) (hβhat : βhat ∈ Set.Ioo 0 1)
    (t : ℝ) (ht : 0 < t) (φ : E → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    TendstoInDistribution
      (fun (N : ℕ) (a : Ω) => ∫ y : E, hN P 𝔏 env βhat N t y a * φ y)
      atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0
        (((Real.sqrt 2 * cBeta βhat) ^ 2 * sigmaSq (t / 2) φ).toNNReal)) := by sorry

end KPZ2D.Polymer
