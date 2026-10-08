-- Prove2me | Theorems.Thm_KernelDRO_Duality_lemma_D_1
-- name    : KernelDRO.Duality.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:38.084453+00:00
-- url     : https://prove2.me/theorems/96ead18d-21aa-4b15-87d8-69b65715f4ec
-- title:
--   Lemma D.1, pp. 22–23 — the conic constraint $l-f-f_0\in-\mathcal K^*$ is equivalent to $l\le f_0+f$ on $\mathcal X$
-- statement:
--   Let $\mathcal X$ be a compact metric space with its Borel $\sigma$-algebra, $\varphi:\mathcal X\to\mathcal H$ a continuous feature map into a real Hilbert space, and $l:\mathcal X\to[-\infty,\infty)$ upper semicontinuous. For $f_0\in\mathbb R$ and $f\in\mathcal H$, the following are equivalent:
--
--   1. $\displaystyle\int\big(l-f_0-f\big)\,dP\le0$ for every Borel probability measure $P$ on $\mathcal X$ (the conic constraint $l-f-f_0\in-\mathcal K^*$, with $\mathcal K^*$ the dual cone of the probability simplex);
--   2. $l(\xi)\le f_0+f(\xi)$ for all $\xi\in\mathcal X$, the semi-infinite constraint (26).
--
--   This turns the dual cone constraint of the Lagrangian derivation into the semi-infinite constraint of the dual problem (12).
--
--   **Formalization Note** The dual cone of the conic hull $\mathrm{co}(\mathcal P)$ is the same as that of $\mathcal P$, since $\int h\,d(cP)=c\int h\,dP$ for $c\ge0$; the statement quantifies over probability measures. The integral of the extended-real function is `erealExpectation`.
-- source:
--   Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, Lemma D.1, (26), pp. 22–23; dual cone defined in App. A, Notation, p. 13

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_KernelDRO_Duality_Setting

open MeasureTheory

namespace KernelDRO.Duality

open WassersteinDRO.Duality

/-- **Lemma D.1** (Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization,
arXiv:2006.06981v3, Lemma D.1, pp. 22–23). The conic constraint `l − f − f₀ ∈ −𝒦*`, where `𝒦*` is
the dual cone of the probability simplex `𝒫`, i.e. `∫ (l − f₀ − f) dP ≤ 0` for every `P`, is
equivalent to the semi-infinite constraint (26): `l(ξ) ≤ f₀ + f(ξ)` for all `ξ ∈ 𝒳`.

**Formalization Note.** The dual cone is that of the conic hull `co(𝒫)` (p. 13: `𝒦* := {h : ∫ h dm ≥ 0,
∀ m ∈ 𝒦}`); since `∫ h d(cP) = c ∫ h dP` for `c ≥ 0`, quantifying over probability measures is the
same constraint, which is the normalization the proof of "⇐" makes. The integral `∫ (l − f₀ − f) dP`
of the extended-real function is `erealExpectation`; `θ` is suppressed (p. 13). Standing
hypotheses: `𝒳` compact metric with its Borel σ-algebra, `φ` continuous, `l` upper
semicontinuous with values in `[−∞, ∞)`. -/
theorem lemma_D_1 {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : X → H) (hφ : Continuous φ) (l : X → EReal) (hl_usc : UpperSemicontinuous l)
    (hl_top : ∀ ξ, l ξ ≠ ⊤) (f₀ : ℝ) (f : H) :
    (∀ P : ProbabilityMeasure X,
        erealExpectation (P : Measure X)
          (fun ξ => l ξ - ((f₀ + rkhsEval φ f ξ : ℝ) : EReal)) ≤ 0) ↔
      IsDualFeasible φ l f₀ f := by sorry

end KernelDRO.Duality
