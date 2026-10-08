-- Prove2me | Theorems.Thm_KPZ2D_Polymer_eq_3_12
-- name    : KPZ2D.Polymer.eq_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:10.670984+00:00
-- url     : https://prove2.me/theorems/dd216c11-9e5c-4b71-9a46-9e760c2ef341
-- title:
--   (3.12), p. 12 — uniform p-th moments for some p > 2: E[Z^p], E[(Z^A)^p] ≤ C′, E|Ẑ^A|^p ≤ C′ a_N^{p/2}
-- statement:
--   Assume the disorder law satisfies (1.19)–(1.20) and fix $\hat\beta\in(0,1)$. With $Z_N(x)$, $Z_N^A(x)$, $\widehat Z_N^A(x)=Z_N(x)-Z_N^A(x)$ and $a_N=1/(\log N)^{1-g}$ as in (1.22), (2.2)–(2.5), there exist $g^*>0$ and an exponent $p=p_{\hat\beta}\in(2,\infty)$ such that for every window exponent $g\in(0,g^*)$ there is a finite constant $C'_{\hat\beta}$ with
--
--   $$\mathbb E\big[Z_N(x)^p\big]\le C'_{\hat\beta},\qquad \mathbb E\big[Z^A_N(x)^p\big]\le C'_{\hat\beta},\qquad \mathbb E\big[|\widehat Z^A_N(x)|^p\big]\le C'_{\hat\beta}\,(a_N)^{p/2}\tag{3.12}$$
--
--   for every $x\in\mathbb Z^2$ and all sufficiently large $N$.
--
--   These are the higher-moment versions of (3.2)–(3.4); the room $p>2$ is what makes uniform integrability arguments available in the proofs of Propositions 2.1 and 2.3.
--
--   **Formalization Note** "For all $N\in\mathbb N$" is weakened to "for all sufficiently large $N$" because (1.19) guarantees $\lambda(\beta)<\infty$ only for small $\beta>0$. The exponent $p$ is chosen before the window exponent $g$, as the page's notation $p_{\hat\beta}$ indicates; the constant may depend on $g$. Moments are extended nonnegative integrals with real powers ($Z_N>0$, so $Z_N^p$ is the usual power).
-- source:
--   Caravenna, Sun, Zygouras, The two-dimensional KPZ equation in the entire subcritical regime, arXiv:1812.03911v3, (3.12), p. 12

import Mathlib
import Definitions.Def_PolymerEndpoint_Atomic_Model
import Definitions.Def_KPZ2D_Polymer_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace KPZ2D.Polymer

/-- Uniform `p`-th moment bounds for some `p > 2`, (3.12), p. 12. -/
theorem eq_3_12 (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (h119 : Assumption119 𝔏) (γ C₁ C₂ : ℝ)
    (h120 : Concentration120 𝔏 γ C₁ C₂)
    (βhat : ℝ) (hβhat : βhat ∈ Set.Ioo 0 1) :
    ∃ γstar : ℝ, 0 < γstar ∧ ∃ p : ℝ, 2 < p ∧ ∀ g ∈ Set.Ioo 0 γstar,
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (env : PolymerEndpoint.Atomic.Cell 2 → Ω → ℝ)
      (henv : PolymerEndpoint.Atomic.IsEnvironment env 𝔏 P),
      ∀ᶠ N : ℕ in atTop, ∀ x : Site,
        (∫⁻ a, ENNReal.ofReal (Z 𝔏 env βhat N x a ^ p) ∂P) ≤ ENNReal.ofReal C ∧
        (∫⁻ a, ENNReal.ofReal (ZA 𝔏 env βhat g N x a ^ p) ∂P) ≤ ENNReal.ofReal C ∧
        (∫⁻ a, ENNReal.ofReal (|Zhat 𝔏 env βhat g N x a| ^ p) ∂P) ≤
          ENNReal.ofReal (C * aN g N ^ (p / 2)) := by sorry

end KPZ2D.Polymer
