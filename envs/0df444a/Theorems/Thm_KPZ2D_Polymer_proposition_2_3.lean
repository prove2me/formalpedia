-- Prove2me | Theorems.Thm_KPZ2D_Polymer_proposition_2_3
-- name    : KPZ2D.Polymer.proposition_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:03.944981+00:00
-- url     : https://prove2.me/theorems/f9bdb23e-8378-4142-8aaa-3d964146b9d6
-- title:
--   Proposition 2.3, p. 8 — late-window replacement in spatially averaged L¹
-- statement:
--   Under the standing disorder assumptions and $\hat\beta\in(0,1)$, choose a sufficiently small early-window exponent $g>0$. Let $\widehat Z_N^A=Z_N-Z_N^A$ and let $Z_N^{B\ge}$ sample disorder only in the late-time window (2.10). For every continuous compactly supported $\phi:\mathbb R^2\to\mathbb R$,
--
--   $$\frac{\sqrt{\log N}}{N}\sum_{x\in\mathbb Z^2}\left(\frac{\widehat Z_N^A(x)}{Z_N^A(x)}-(Z_N^{B\ge}(x)-1)\right)\phi(x/\sqrt N)\longrightarrow0\quad\text{in }L^1(\mathbb P).\tag{2.13}$$
--
--   This identifies the late-window partition function as the relevant fluctuation term.
--
--   **Formalization Note** The $L^1$ norm is an extended nonnegative integral. The denominators are positive for the finite-horizon polymer, and the compact support makes the spatial sum finite.
-- source:
--   Caravenna, Sun, Zygouras, The two-dimensional KPZ equation in the entire subcritical regime, arXiv:1812.03911v3, Proposition 2.3, (2.13), p. 8

import Mathlib
import Definitions.Def_PolymerEndpoint_Atomic_Model
import Definitions.Def_KPZ2D_Polymer_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace KPZ2D.Polymer

/-- The normalized remainder is replaced by the late window in averaged L¹, Proposition 2.3. -/
theorem proposition_2_3 (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
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
            |Real.sqrt (Real.log N) * (1 / (N : ℝ)) *
              ∑' x : Site,
                (Zhat 𝔏 env βhat g N x a / ZA 𝔏 env βhat g N x a -
                  (ZB 𝔏 env βhat g N x a - 1)) *
                  φ ((Real.sqrt N)⁻¹ • toE x)| ∂P) atTop (𝓝 0) := by sorry

end KPZ2D.Polymer
