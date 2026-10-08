-- Prove2me | Theorems.Thm_KPZ2D_Polymer_proposition_3_1
-- name    : KPZ2D.Polymer.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:55.546348+00:00
-- url     : https://prove2.me/theorems/a70619a0-1c15-4860-8e2c-1a37481fbc0a
-- title:
--   Proposition 3.1, p. 13 — stretched-exponential left tail of restricted partition functions
-- statement:
--   Assume (1.19) and the concentration property (1.20), whose exponent is $\gamma>1$, and fix $\hat\beta\in(0,1)$. There is a finite $c>0$ such that for every sufficiently large $N$, every $\Lambda\subseteq\{1,\ldots,N\}\times\mathbb Z^2$, and every $t\ge0$,
--
--   $$\mathbb P\big(\log Z_{\Lambda,\beta_N}(0)\le-t\big)\le c\exp(-t^\gamma/c).\tag{3.13}$$
--
--   Uniformity over the allowed disorder sets supports the negative-moment estimates for both the full and early-window partition functions.
--
--   **Formalization Note** The bound starts at sufficiently large $N$, as (1.19) guarantees $\lambda(\beta_N)<\infty$ only eventually. The restricted partition function has horizon $N$ and reads no time-zero disorder.
-- source:
--   Caravenna, Sun, Zygouras, The two-dimensional KPZ equation in the entire subcritical regime, arXiv:1812.03911v3, Proposition 3.1, (3.13), p. 13

import Mathlib
import Definitions.Def_PolymerEndpoint_Atomic_Model
import Definitions.Def_KPZ2D_Polymer_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace KPZ2D.Polymer

/-- The uniform left-tail bound, Proposition 3.1, p. 13. -/
theorem proposition_3_1 (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (h119 : Assumption119 𝔏) (γ C₁ C₂ : ℝ)
    (h120 : Concentration120 𝔏 γ C₁ C₂)
    (βhat : ℝ) (hβhat : βhat ∈ Set.Ioo 0 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (env : PolymerEndpoint.Atomic.Cell 2 → Ω → ℝ)
      (henv : PolymerEndpoint.Atomic.IsEnvironment env 𝔏 P),
      ∀ᶠ N : ℕ in atTop,
      ∀ Λ : Set (PolymerEndpoint.Atomic.Cell 2),
        Λ ⊆ {u | 1 ≤ u.1 ∧ u.1 ≤ N} →
        ∀ t : ℝ, 0 ≤ t →
          P {a | Real.log (ZLam 𝔏 (fun u => env u a) Λ (betaN βhat N) N 0) ≤ -t} ≤
            ENNReal.ofReal (c * Real.exp (-(t ^ γ) / c)) := by sorry

end KPZ2D.Polymer
