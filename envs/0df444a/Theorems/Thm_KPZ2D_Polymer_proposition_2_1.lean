-- Prove2me | Theorems.Thm_KPZ2D_Polymer_proposition_2_1
-- name    : KPZ2D.Polymer.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:59.957892+00:00
-- url     : https://prove2.me/theorems/3fb67669-f9ec-4b13-9abf-e7b374ee5320
-- title:
--   Proposition 2.1, p. 8 — averaged logarithmic linearization error vanishes in L²
-- statement:
--   Under the standing disorder assumptions and $\hat\beta\in(0,1)$, choose a sufficiently small early-window exponent $g>0$. For any continuous compactly supported $\phi:\mathbb R^2\to\mathbb R$, let $O_N(x)$ be the error in the logarithmic decomposition (2.7). Then
--
--   $$\frac{\sqrt{\log N}}{N}\sum_{x\in\mathbb Z^2}\big(O_N(x)-\mathbb E[O_N(x)]\big)\phi(x/\sqrt N)\longrightarrow 0\quad\text{in }L^2(\mathbb P).\tag{2.8}$$
--
--   It removes the nonlinear error from the spatially averaged fluctuation field.
--
--   **Formalization Note** The $L^2$ norm uses an extended nonnegative second-moment integral, avoiding the default value of a nonintegrable Bochner integral. Compact support makes each spatial sum finite.
-- source:
--   Caravenna, Sun, Zygouras, The two-dimensional KPZ equation in the entire subcritical regime, arXiv:1812.03911v3, Proposition 2.1, (2.8), p. 8

import Mathlib
import Definitions.Def_PolymerEndpoint_Atomic_Model
import Definitions.Def_KPZ2D_Polymer_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace KPZ2D.Polymer

/-- Spatially averaged linearization error vanishes in L², Proposition 2.1, p. 8. -/
theorem proposition_2_1 (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
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
                (O 𝔏 env βhat g N x a - ∫ b, O 𝔏 env βhat g N x b ∂P) *
                  φ ((Real.sqrt N)⁻¹ • toE x)) ^ 2) ∂P) atTop (𝓝 0) := by sorry

end KPZ2D.Polymer
