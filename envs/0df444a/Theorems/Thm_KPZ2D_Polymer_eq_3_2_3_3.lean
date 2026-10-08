-- Prove2me | Theorems.Thm_KPZ2D_Polymer_eq_3_2_3_3
-- name    : KPZ2D.Polymer.eq_3_2_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:50.531429+00:00
-- url     : https://prove2.me/theorems/149282f5-8b90-482e-97af-a1f5a709b2ce
-- title:
--   (3.2)–(3.3), p. 11 — uniform second moments of full and early-window partition functions
-- statement:
--   Under the disorder assumptions (1.19)–(1.20), fix $\hat\beta\in(0,1)$. There is a finite positive constant $C_{\hat\beta}$, uniform in the early-window exponent $g\in(0,1)$, the starting site $x\in\mathbb Z^2$, and all sufficiently large $N$, such that
--
--   $$\mathbb E[Z_N(x)^2]\le C_{\hat\beta},\qquad \mathbb E[(Z_N^A(x))^2]\le C_{\hat\beta}.\tag{3.2–3.3}$$
--
--   These bounds control the full polymer and every early-window restriction in the subcritical regime.
--
--   **Formalization Note** The bounds are stated for all sufficiently large $N$: (1.19) guarantees a finite logarithmic moment generating function only at sufficiently small positive arguments. Extended nonnegative integrals preserve the meaning of second moments even before integrability is known.
-- source:
--   Caravenna, Sun, Zygouras, The two-dimensional KPZ equation in the entire subcritical regime, arXiv:1812.03911v3, (3.2)–(3.3), p. 11

import Mathlib
import Definitions.Def_PolymerEndpoint_Atomic_Model
import Definitions.Def_KPZ2D_Polymer_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace KPZ2D.Polymer

/-- The second-moment bounds (3.2)–(3.3), p. 11. -/
theorem eq_3_2_3_3 (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (h119 : Assumption119 𝔏) (γ C₁ C₂ : ℝ)
    (h120 : Concentration120 𝔏 γ C₁ C₂)
    (βhat : ℝ) (hβhat : βhat ∈ Set.Ioo 0 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (env : PolymerEndpoint.Atomic.Cell 2 → Ω → ℝ)
      (henv : PolymerEndpoint.Atomic.IsEnvironment env 𝔏 P),
      ∀ᶠ N : ℕ in atTop, ∀ g ∈ Set.Ioo 0 1, ∀ x : Site,
      (∫⁻ a, ENNReal.ofReal (Z 𝔏 env βhat N x a ^ 2) ∂P) ≤ ENNReal.ofReal C ∧
      (∫⁻ a, ENNReal.ofReal (ZA 𝔏 env βhat g N x a ^ 2) ∂P) ≤ ENNReal.ofReal C := by sorry

end KPZ2D.Polymer
