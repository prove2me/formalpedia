-- Prove2me | Theorems.Thm_KPZ2D_Polymer_eq_3_14_3_16
-- name    : KPZ2D.Polymer.eq_3_14_3_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:03.799242+00:00
-- url     : https://prove2.me/theorems/c5465bae-282b-4cab-b68c-10a2c8ec962b
-- title:
--   (3.14)–(3.16), p. 13 — uniform negative moments of Z and Z^A and moments of |log Z^A|
-- statement:
--   Assume the disorder law satisfies (1.19)–(1.20) and fix $\hat\beta\in(0,1)$. With $Z_N(x)$ the polymer partition function started at $x$ and $Z_N^A(x)$ its restriction to the early window $A_N^x$ of (2.3), there is a threshold $g^*>0$ such that for every $p\in(0,\infty)$ there is a finite constant $C_{p,\hat\beta}$ such that the following bounds hold for every window exponent $g\in(0,g^*)$, every $x\in\mathbb Z^2$ and all sufficiently large $N$:
--
--   $$\mathbb E\big[Z_N(x)^{-p}\big]\le C_{p,\hat\beta},\qquad \mathbb E\big[Z^A_N(x)^{-p}\big]\le C_{p,\hat\beta},\qquad \mathbb E\big[|\log Z^A_N(x)|^{p}\big]\le C_{p,\hat\beta}.\tag{3.14–3.16}$$
--
--   The page derives these from the left-tail bound of Proposition 3.1 with $\Lambda=\{1,\dots,N\}\times\mathbb Z^2$ and $\Lambda=A_N^x$. They make $\log Z_N$ and $\log Z_N^A$ integrable to every order, uniformly in $N$.
--
--   **Formalization Note** "$\sup_{N\in\mathbb N}$" is weakened to "for all sufficiently large $N$" because (1.19) guarantees $\lambda(\beta)<\infty$ only for small $\beta>0$. Proposition 3.1 is uniform over all $\Lambda\subseteq\{1,\dots,N\}\times\mathbb Z^2$, so one constant works uniformly over the allowed window exponents $g\in(0,g^*)$ of (2.2), which the page fixes once. Moments are extended nonnegative integrals with real powers.
-- source:
--   Caravenna, Sun, Zygouras, The two-dimensional KPZ equation in the entire subcritical regime, arXiv:1812.03911v3, (3.14)–(3.16), p. 13

import Mathlib
import Definitions.Def_PolymerEndpoint_Atomic_Model
import Definitions.Def_KPZ2D_Polymer_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace KPZ2D.Polymer

/-- Uniform negative moments and logarithmic moments, (3.14)–(3.16), p. 13. -/
theorem eq_3_14_3_16 (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (h119 : Assumption119 𝔏) (γ C₁ C₂ : ℝ)
    (h120 : Concentration120 𝔏 γ C₁ C₂)
    (βhat : ℝ) (hβhat : βhat ∈ Set.Ioo 0 1) :
    ∃ γstar : ℝ, 0 < γstar ∧ ∀ p : ℝ, 0 < p →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (env : PolymerEndpoint.Atomic.Cell 2 → Ω → ℝ)
      (henv : PolymerEndpoint.Atomic.IsEnvironment env 𝔏 P),
      ∀ᶠ N : ℕ in atTop, ∀ g ∈ Set.Ioo 0 γstar, ∀ x : Site,
        (∫⁻ a, ENNReal.ofReal (Z 𝔏 env βhat N x a ^ (-p)) ∂P) ≤ ENNReal.ofReal C ∧
        (∫⁻ a, ENNReal.ofReal (ZA 𝔏 env βhat g N x a ^ (-p)) ∂P) ≤ ENNReal.ofReal C ∧
        (∫⁻ a, ENNReal.ofReal (|Real.log (ZA 𝔏 env βhat g N x a)| ^ p) ∂P) ≤
          ENNReal.ofReal C := by sorry

end KPZ2D.Polymer
