-- Prove2me | Theorems.Thm_KernelDRO_Duality_reproducing_identity
-- name    : KernelDRO.Duality.reproducing_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:50.029824+00:00
-- url     : https://prove2.me/theorems/1185f1d5-ef5a-428b-a463-495c3678e323
-- title:
--   App. A, Notation, p. 13 — $\int f\,dP=\langle f,\mu_P\rangle_{\mathcal H}$
-- statement:
--   Let $\mathcal X$ be a compact metric space with its Borel $\sigma$-algebra, $\mathcal H$ a real Hilbert space and $\varphi:\mathcal X\to\mathcal H$ a continuous feature map. For every $f\in\mathcal H$ and every Borel probability measure $P$ on $\mathcal X$,
--   $$\int_{\mathcal X} f(\xi)\,dP(\xi)=\langle f,\mu_P\rangle_{\mathcal H},\qquad f(\xi)=\langle f,\varphi(\xi)\rangle_{\mathcal H},\quad \mu_P=\int\varphi\,dP .$$
--   The expectation of any RKHS function is thus the inner product with the mean embedding; the paper uses this identity throughout its proofs, in particular to rewrite the Lagrangian (13).
--
--   **Formalization Note** Both integrals are Bochner integrals; continuity of $\varphi$ on the compact $\mathcal X$ makes them genuine.
-- source:
--   Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, App. A, Notation, p. 13

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_KernelDRO_Duality_Setting

open MeasureTheory

namespace KernelDRO.Duality

open WassersteinDRO.Duality

/-- **Reproducing identity** `∫ f dP = ⟨f, µ_P⟩_ℋ` for `f ∈ ℋ` and `P ∈ 𝒫` (Zhu, Jitkrittum, Diehl &
Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, App. A, Notation, p. 13):
integrating the RKHS function `ξ ↦ f(ξ) = ⟪f, φ ξ⟫` against a Borel probability measure `P` on the
compact space `𝒳` gives the inner product of `f` with the mean embedding `µ_P = ∫ φ dP`.

**Formalization Note.** `𝒳` is a compact metric space with its Borel σ-algebra (a compact
`𝒳 ⊂ ℝᵈ` is an instance) and the feature map `φ` is continuous (equivalently, the kernel
`k(x, y) = ⟪φ x, φ y⟫` is continuous), so both integrals are genuine Bochner integrals. -/
theorem reproducing_identity {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : X → H) (hφ : Continuous φ) (f : H) (P : ProbabilityMeasure X) :
    ∫ ξ, rkhsEval φ f ξ ∂(P : Measure X) = inner ℝ f (meanEmbedding φ P) := by sorry

end KernelDRO.Duality
