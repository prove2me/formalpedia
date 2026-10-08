-- Prove2me | Theorems.Thm_KernelDRO_Duality_weak_duality
-- name    : KernelDRO.Duality.weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:53.452994+00:00
-- url     : https://prove2.me/theorems/2ccb249e-a3e4-4a7c-aec1-089ad187a173
-- title:
--   p. 6 (and proof of Prop. A.1, p. 14) — weak duality $\int l\,dP\le f_0+\delta^*_{\mathcal C}(f)$
-- statement:
--   Let $\mathcal X$ be a compact metric space with its Borel $\sigma$-algebra, $\varphi:\mathcal X\to\mathcal H$ continuous, $\mathcal C\subseteq\mathcal H$ any set, and $l:\mathcal X\to[-\infty,\infty)$ upper semicontinuous. If $P\in\mathcal K_{\mathcal C}$ (that is, $\mu_P\in\mathcal C$) and $(f_0,f)\in\mathbb R\times\mathcal H$ satisfies $l(\xi)\le f_0+f(\xi)$ for all $\xi\in\mathcal X$, then
--   $$\int l\,dP\ \le\ f_0+\delta^*_{\mathcal C}(f).$$
--   Taking the supremum over $P$ and the infimum over $(f_0,f)$ gives weak duality $\mathrm{(P)}\le\mathrm{(D)}$ for (11) and (12); the right-hand side is a computable bound on the worst-case risk.
--
--   **Formalization Note** $\int l\,dP$ is `erealExpectation`; $\delta^*_{\mathcal C}$ is extended-real valued.
-- source:
--   Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, §3.2, p. 6; Lagrangian (13) in the proof of Proposition A.1, p. 14

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_KernelDRO_Duality_Setting

open MeasureTheory

namespace KernelDRO.Duality

open WassersteinDRO.Duality

/-- **Weak duality** of (11) and (12) (Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally
Robust Optimization, arXiv:2006.06981v3, §3.2, p. 6, "By the weak duality (P) ≤ (D) of (11) and
(12), we have ∫ l dP ≤ f₀ + δ*_𝒞(f)"; derived from the Lagrangian (13) in the proof of Proposition
A.1, p. 14). For every `P` in the ambiguity set `𝒦_𝒞` and every dual feasible `(f₀, f)`,
`∫ l dP ≤ f₀ + δ*_𝒞(f)`. Taking the supremum over `P` and the infimum over `(f₀, f)` gives
`(P) ≤ (D)`.

**Formalization Note.** `∫ l dP` is `erealExpectation` and `δ*_𝒞` is the `EReal` support function.
Standing hypotheses: `𝒳` compact metric with its Borel σ-algebra, `φ` continuous, `l` upper
semicontinuous with values in `[−∞, ∞)`. No hypothesis on `𝒞` is needed. -/
theorem weak_duality {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : X → H) (hφ : Continuous φ) (C : Set H) (l : X → EReal) (hl_usc : UpperSemicontinuous l)
    (hl_top : ∀ ξ, l ξ ≠ ⊤) (P : ProbabilityMeasure X) (hP : P ∈ ambiguitySet φ C) (f₀ : ℝ)
    (f : H) (hfeas : IsDualFeasible φ l f₀ f) :
    erealExpectation (P : Measure X) l ≤ (f₀ : EReal) + supportFun C f := by sorry

end KernelDRO.Duality
