-- Prove2me | Theorems.Thm_KPZ2D_Polymer_proposition_2_4
-- name    : KPZ2D.Polymer.proposition_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:01.400645+00:00
-- url     : https://prove2.me/theorems/b54a263c-59d4-4e3e-9b47-d7fc9d0980f8
-- title:
--   Proposition 2.4, p. 9 — Gaussian limit of the late-window partition function
-- statement:
--   Under the standing disorder assumptions and $\hat\beta\in(0,1)$, choose a sufficiently small early-window exponent $g>0$. For every continuous compactly supported $\phi:\mathbb R^2\to\mathbb R$,
--
--   $$\frac{\sqrt{\log N}}{\sqrt\pi\,\hat\beta}\frac1N\sum_{x\in\mathbb Z^2}(Z_N^{B\ge}(x)-1)\phi(x/\sqrt N)\xrightarrow{d}\langle v^{(\sqrt2c_{\hat\beta})}(1/2,\cdot),\phi\rangle.\tag{2.14}$$
--
--   The limit is centred Gaussian with variance $(\sqrt2c_{\hat\beta})^2\sigma_\phi^2(1/2)$, where the covariance kernel is (1.14). This is the Gaussian input to the polymer fluctuation theorem.
--
--   **Formalization Note** The tested limit is represented by its Gaussian law, including the exact time $1/2$ and normalization $\sqrt{\log N}/(\sqrt\pi\hat\beta)$. The page omits the test-function class here; its proof and Proposition 4.1 use continuous compactly supported $\phi$.
-- source:
--   Caravenna, Sun, Zygouras, The two-dimensional KPZ equation in the entire subcritical regime, arXiv:1812.03911v3, Proposition 2.4, (2.14), p. 9

import Mathlib
import Definitions.Def_PolymerEndpoint_Atomic_Model
import Definitions.Def_KPZ2D_Polymer_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace KPZ2D.Polymer

/-- The late-window partition function has the Gaussian limit, Proposition 2.4, p. 9. -/
theorem proposition_2_4 (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (h119 : Assumption119 𝔏) (γ C₁ C₂ : ℝ)
    (h120 : Concentration120 𝔏 γ C₁ C₂)
    (βhat : ℝ) (hβhat : βhat ∈ Set.Ioo 0 1) :
    ∃ γstar : ℝ, 0 < γstar ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (env : PolymerEndpoint.Atomic.Cell 2 → Ω → ℝ)
      (henv : PolymerEndpoint.Atomic.IsEnvironment env 𝔏 P),
      ∀ g ∈ Set.Ioo 0 γstar,
      ∀ (φ : E → ℝ), Continuous φ → HasCompactSupport φ →
        TendstoInDistribution
          (fun (N : ℕ) (a : Ω) =>
            Real.sqrt (Real.log N) / (Real.sqrt Real.pi * βhat) *
              (1 / (N : ℝ)) *
                ∑' x : Site,
                  (ZB 𝔏 env βhat g N x a - 1) *
                    φ ((Real.sqrt N)⁻¹ • toE x))
          atTop (id : ℝ → ℝ) (fun _ => P)
          (gaussianReal 0
            (((Real.sqrt 2 * cBeta βhat) ^ 2 * sigmaSq (1 / 2) φ).toNNReal)) := by sorry

end KPZ2D.Polymer
