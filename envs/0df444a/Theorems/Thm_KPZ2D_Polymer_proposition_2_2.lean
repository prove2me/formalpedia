-- Prove2me | Theorems.Thm_KPZ2D_Polymer_proposition_2_2
-- name    : KPZ2D.Polymer.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:56.085427+00:00
-- url     : https://prove2.me/theorems/e0ad9b8c-9a20-4ac3-b2b9-4168dc5112f4
-- title:
--   Proposition 2.2, p. 8 — averaged early-window log partition vanishes in L²
-- statement:
--   Under the standing disorder assumptions and $\hat\beta\in(0,1)$, choose a sufficiently small early-window exponent $g>0$. For every continuous compactly supported $\phi:\mathbb R^2\to\mathbb R$,
--
--   $$\frac{\sqrt{\log N}}{N}\sum_{x\in\mathbb Z^2}\big(\log Z_N^A(x)-\mathbb E[\log Z_N^A(x)]\big)\phi(x/\sqrt N)\longrightarrow 0\quad\text{in }L^2(\mathbb P).\tag{2.9}$$
--
--   The early disorder window contributes negligibly to the averaged log-partition fluctuations.
--
--   **Formalization Note** The test function is continuous and compactly supported. The $L^2$ statement is expressed through the extended nonnegative integral of the square.
-- source:
--   Caravenna, Sun, Zygouras, The two-dimensional KPZ equation in the entire subcritical regime, arXiv:1812.03911v3, Proposition 2.2, (2.9), p. 8

import Mathlib
import Definitions.Def_PolymerEndpoint_Atomic_Model
import Definitions.Def_KPZ2D_Polymer_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace KPZ2D.Polymer

/-- The early-window log partition has negligible averaged fluctuations, Proposition 2.2. -/
theorem proposition_2_2 (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (h119 : Assumption119 𝔏) (γ C₁ C₂ : ℝ)
    (h120 : Concentration120 𝔏 γ C₁ C₂)
    (βhat : ℝ) (hβhat : βhat ∈ Set.Ioo 0 1) :
    ∃ γstar : ℝ, 0 < γstar ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (env : PolymerEndpoint.Atomic.Cell 2 → Ω → ℝ)
      (henv : PolymerEndpoint.Atomic.IsEnvironment env 𝔏 P),
      ∀ g ∈ Set.Ioo 0 γstar,
      ∀ (φ : E → ℝ), Continuous φ → HasCompactSupport φ →
        Tendsto (fun N : ℕ =>
          ∫⁻ a, ENNReal.ofReal
            ((Real.sqrt (Real.log N) * (1 / (N : ℝ)) *
              ∑' x : Site,
                (Real.log (ZA 𝔏 env βhat g N x a) -
                    ∫ b, Real.log (ZA 𝔏 env βhat g N x b) ∂P) *
                  φ ((Real.sqrt N)⁻¹ • toE x)) ^ 2) ∂P) atTop (𝓝 0) := by sorry

end KPZ2D.Polymer
