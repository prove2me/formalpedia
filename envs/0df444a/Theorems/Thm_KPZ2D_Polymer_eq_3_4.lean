-- Prove2me | Theorems.Thm_KPZ2D_Polymer_eq_3_4
-- name    : KPZ2D.Polymer.eq_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:59.608506+00:00
-- url     : https://prove2.me/theorems/4e4fc7f9-6916-441e-88c6-33aa922f3448
-- title:
--   (3.4), p. 11 — early-window remainder has second moment of order a_N
-- statement:
--   Assume the disorder law satisfies (1.19)–(1.20) and fix $\hat\beta\in(0,1)$. Let $Z_N(x)=Z_{N,\beta_N}(x)$ be the polymer partition function started at $x\in\mathbb Z^2$, $Z^A_N(x)$ its restriction to the early space–time window $A_N^x$ of (2.3), and $\widehat Z^A_N(x)=Z_N(x)-Z^A_N(x)$ the remainder (2.5). The window is governed by the scale $a_N=1/(\log N)^{1-g}$ of (2.2).
--
--   There is $g^*>0$ such that for every window exponent $g\in(0,g^*)$ there is a finite constant $C_{\hat\beta}>0$ with
--
--   $$\mathbb E\big[\widehat Z^A_N(x)^2\big]\le C_{\hat\beta}\,a_N\qquad\text{for all } x\in\mathbb Z^2 \text{ and all sufficiently large } N.\tag{3.4}$$
--
--   Since $a_N\to0$, the remainder is small in $L^2$ at a fixed site, which is what justifies the linearization $\log Z_N\approx\log Z_N^A+\widehat Z_N^A/Z_N^A$ of (2.6).
--
--   **Formalization Note** The page fixes $g\in(0,\gamma^*)$ once in (2.2), with $\gamma^*$ depending only on $\hat\beta$; the Lean statement asserts the existence of such a $g^*$ and lets the constant depend on $g$, never on $N$, $x$ or the probability space. "For all $N\in\mathbb N$" is weakened to "for all sufficiently large $N$" because (1.19) only guarantees $\lambda(\beta)<\infty$ for small $\beta>0$, and $\lambda(\beta_N)$ enters $Z_N$. The second moment is an extended nonnegative integral, so non-integrability cannot make the bound vacuous. The window exponent $g$ is the paper's $\gamma$ of (2.2), renamed to keep it apart from the concentration exponent $\gamma$ of (1.20).
-- source:
--   Caravenna, Sun, Zygouras, The two-dimensional KPZ equation in the entire subcritical regime, arXiv:1812.03911v3, (3.4), p. 11

import Mathlib
import Definitions.Def_PolymerEndpoint_Atomic_Model
import Definitions.Def_KPZ2D_Polymer_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace KPZ2D.Polymer

/-- The sharper remainder second-moment bound (3.4), p. 11. -/
theorem eq_3_4 (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (h119 : Assumption119 𝔏) (γ C₁ C₂ : ℝ)
    (h120 : Concentration120 𝔏 γ C₁ C₂)
    (βhat : ℝ) (hβhat : βhat ∈ Set.Ioo 0 1) :
    ∃ γstar : ℝ, 0 < γstar ∧ ∀ g ∈ Set.Ioo 0 γstar,
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (env : PolymerEndpoint.Atomic.Cell 2 → Ω → ℝ)
      (henv : PolymerEndpoint.Atomic.IsEnvironment env 𝔏 P),
      ∀ᶠ N : ℕ in atTop, ∀ x : Site,
        (∫⁻ a, ENNReal.ofReal (Zhat 𝔏 env βhat g N x a ^ 2) ∂P) ≤
          ENNReal.ofReal (C * aN g N) := by sorry

end KPZ2D.Polymer
