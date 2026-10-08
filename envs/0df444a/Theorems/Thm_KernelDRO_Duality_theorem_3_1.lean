-- Prove2me | Theorems.Thm_KernelDRO_Duality_theorem_3_1
-- name    : KernelDRO.Duality.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:27:37.168869+00:00
-- url     : https://prove2.me/theorems/f9bed297-4a14-4d7b-8734-04ad57fb16cf
-- title:
--   Theorem 3.1 (Generalized Duality), p. 5 — the Kernel DRO primal (2) equals the dual (4)
-- statement:
--   Let $\mathcal X$ be a compact metric space with its Borel $\sigma$-algebra and $\mathcal P$ the set of Borel probability measures on $\mathcal X$. Let $\mathcal H$ be a real Hilbert space with a continuous feature map $\varphi:\mathcal X\to\mathcal H$, so that $f\in\mathcal H$ acts by $f(\xi)=\langle f,\varphi(\xi)\rangle_{\mathcal H}$, and let $\mathcal C\subseteq\mathcal H$ be closed and convex with nonempty ambiguity set $\mathcal K_{\mathcal C}=\{P\in\mathcal P:\int\varphi\,dP\in\mathcal C\}$. Let $\Theta$ be any set of decisions and $l:\Theta\times\mathcal X\to[-\infty,\infty)$ a loss such that every $l(\theta,\cdot)$ is upper semicontinuous and proper (not identically $-\infty$). Then
--
--   1. for every $\theta\in\Theta$,
--   $$\sup_{P\in\mathcal K_{\mathcal C}}\int l(\theta,\xi)\,dP(\xi)\;=\;\inf\Big\{f_0+\delta^*_{\mathcal C}(f):\ f_0\in\mathbb R,\ f\in\mathcal H,\ l(\theta,\xi)\le f_0+f(\xi)\ \forall\xi\in\mathcal X\Big\},$$
--   where $\delta^*_{\mathcal C}(f)=\sup_{\mu\in\mathcal C}\langle f,\mu\rangle_{\mathcal H}$ is the support function of $\mathcal C$;
--   2. consequently the Kernel DRO problem (2) and its dual (4) have the same value:
--   $$\mathrm{(P)}:=\inf_\theta\sup_{P\in\mathcal K_{\mathcal C}}\int l(\theta,\xi)\,dP(\xi)\;=\;\inf_{\theta,\,f_0,\,f}\Big\{f_0+\delta^*_{\mathcal C}(f):\ l(\theta,\cdot)\le f_0+f\text{ on }\mathcal X\Big\}=:\mathrm{(D)}.$$
--
--   The worst-case expected loss over a set of distributions described through their kernel mean embeddings is thus computed by a single minimization over an RKHS function $f_0+f$ that majorizes the loss; no Lipschitz constant or RKHS norm of $l$ is needed.
--
--   **Formalization Note** $\int l\,dP$ is the published extended-real expectation `erealExpectation`; all values are extended reals. The paper's Slater clause $\mathrm{ri}(\mathcal K_{\mathcal C})\ne\emptyset$ names no topology on measures and is used in the proof only to guarantee a primal solution (p. 15); it is read as $\mathcal K_{\mathcal C}\ne\emptyset$, which it implies, so the statement is at least as strong as the paper's. Continuity of $\varphi$ (equivalently of the kernel) is not in Assumption 3.1 but is used by Appendix D. Every printed "min" is read as an infimum: dual attainment is not proved and can fail. A compact $\mathcal X\subset\mathbb R^d$ is an instance of the compact metric space.
-- source:
--   Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, Theorem 3.1, (2), (4), pp. 3, 5; Assumption 3.1, p. 3; proof via Proposition A.1 and (15), p. 16

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_KernelDRO_Duality_Setting

open MeasureTheory

namespace KernelDRO.Duality

open WassersteinDRO.Duality

/-- **Theorem 3.1** (Generalized Duality) (Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally
Robust Optimization, arXiv:2006.06981v3, Theorem 3.1, p. 5; proved on p. 16 from Proposition A.1 by
(15)). Under Assumption 3.1, the Kernel DRO problem
`(P) := min_θ sup_{P,µ} {∫ l(θ, ξ) dP(ξ) : ∫ φ dP = µ, P ∈ 𝒫, µ ∈ 𝒞}` (2) is equivalent to
`(D) := min_{θ, f₀∈ℝ, f∈ℋ} f₀ + δ*_𝒞(f)` subject to `l(θ, ξ) ≤ f₀ + f(ξ), ∀ ξ ∈ 𝒳` (4), where
`δ*_𝒞(f) := sup_{µ∈𝒞} ⟨f, µ⟩_ℋ`; i.e. `(P) = (D)`, and strong duality holds for the inner moment
problem for every `θ` pointwise.

**Formalization Note.** The decision variable `θ` ranges over an arbitrary type `Θ` ("The theorem
holds regardless of the dependency of l on θ", p. 5) and the loss is `l : Θ → 𝒳 → [−∞, ∞)`. Standing
hypotheses (Assumption 3.1, p. 3, and §2, p. 2): `𝒳` is a compact metric space with its Borel
σ-algebra (a compact `𝒳 ⊂ ℝᵈ` is an instance); the RKHS is in feature-map form, a real Hilbert space
`ℋ` with a continuous feature map `φ` (continuity of the kernel is not written in Assumption 3.1 but
is used by §D.2 through a universal, hence continuous, kernel); `𝒞 ⊆ ℋ` is closed and convex; every
`l(θ, ·)` is upper semicontinuous, never `+∞`, and proper (not identically `−∞`, p. 2). The Slater
clause "ri(𝒦_𝒞) ≠ ∅" names no topology on measures and is used in the proof only as "the primal
problem has a non-empty solution set" (p. 15); it is read as `𝒦_𝒞 ≠ ∅`, which it implies under any
reading, so this statement is at least as strong as the paper's. Every "min" (the outer `min_θ` of
(2) and (4) and the inner `min_{f₀, f}`) is read as an infimum: dual attainment is not proved in the
paper and can fail. `∫ l dP` is the published `erealExpectation` and all values are extended
reals. The first conjunct is the pointwise strong duality, the second the literal `(P) = (D)`. -/
theorem theorem_3_1 {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Θ : Type*} (φ : X → H) (hφ : Continuous φ) (C : Set H) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (l : Θ → X → EReal) (hl_usc : ∀ θ, UpperSemicontinuous (l θ))
    (hl_top : ∀ θ ξ, l θ ξ ≠ ⊤) (hl_proper : ∀ θ, ∃ ξ, l θ ξ ≠ ⊥)
    (hK : (ambiguitySet φ C).Nonempty) :
    (∀ θ, primalValue φ C (l θ) = dualValue φ C (l θ)) ∧
      (⨅ θ, primalValue φ C (l θ)) = ⨅ θ, dualValue φ C (l θ) := by sorry

end KernelDRO.Duality
