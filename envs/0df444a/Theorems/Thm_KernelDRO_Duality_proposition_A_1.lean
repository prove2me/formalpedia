-- Prove2me | Theorems.Thm_KernelDRO_Duality_proposition_A_1
-- name    : KernelDRO.Duality.proposition_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:52.949546+00:00
-- url     : https://prove2.me/theorems/2f322b56-023a-4844-8407-200063688643
-- title:
--   Proposition A.1, p. 13 — strong duality for the inner moment problem (11)
-- statement:
--   Under the standing hypotheses below (Assumption 3.1), the inner moment problem
--   $$\sup_{P\in\mathcal P,\ \mu\in\mathcal C}\int l\,dP\quad\text{subject to}\quad\int\varphi\,dP=\mu\tag{11}$$
--   has the same optimal value as
--   $$\inf_{f_0\in\mathbb R,\ f\in\mathcal H}\ \delta^*_{\mathcal C}(f)+f_0\quad\text{subject to}\quad l(\xi)\le f_0+f(\xi)\ \ \forall\xi\in\mathcal X,\tag{12}$$
--   where $\delta^*_{\mathcal C}$ is the support function of $\mathcal C$: strong duality holds. The two values are extended reals and the equality includes the case where both are $-\infty$.
--
--   **Standing hypotheses.** $\mathcal X$ is a compact metric space with its Borel $\sigma$-algebra and $\mathcal P$ is the set of Borel probability measures on $\mathcal X$. $\mathcal H$ is a real Hilbert space with a continuous feature map $\varphi:\mathcal X\to\mathcal H$, and $f\in\mathcal H$ acts on $\mathcal X$ by the reproducing property $f(\xi)=\langle f,\varphi(\xi)\rangle_{\mathcal H}$. The set $\mathcal C\subseteq\mathcal H$ is closed and convex, the ambiguity set $\mathcal K_{\mathcal C}=\{P\in\mathcal P:\mu_P\in\mathcal C\}$ with $\mu_P=\int\varphi\,dP$ is nonempty, and the loss $l:\mathcal X\to[-\infty,\infty)$ is upper semicontinuous and proper (not identically $-\infty$).
--
--   **Formalization Note** $\int l\,dP$ is the published extended-real expectation `erealExpectation`, which for an upper semicontinuous loss on a compact space is the usual $\int l\,dP\in[-\infty,\infty)$. The Slater clause $\mathrm{ri}(\mathcal K_{\mathcal C})\neq\emptyset$ of Assumption 3.1 is read as $\mathcal K_{\mathcal C}\neq\emptyset$, the only use the proof makes of it (p. 15). Continuity of $\varphi$ (equivalently of the kernel) is not written in Assumption 3.1 but is used by Appendix D through a universal, hence continuous, kernel. A compact $\mathcal X\subset\mathbb R^d$ is an instance of the compact metric space. The paper writes "min" in (12); its proof only produces $\epsilon$-optimal dual solutions, so the dual value is an infimum and no attainment is claimed.
-- source:
--   Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, Proposition A.1, (11), (12), p. 13; proof pp. 14–15

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_KernelDRO_Duality_Setting

open MeasureTheory

namespace KernelDRO.Duality

open WassersteinDRO.Duality

/-- **Proposition A.1** (Strong dual to (11)) (Zhu, Jitkrittum, Diehl & Schölkopf, Kernel
Distributionally Robust Optimization, arXiv:2006.06981v3, Proposition A.1, p. 13; proof pp. 14–15).
Under Assumption 3.1, the inner moment problem (11),
`sup_{P∈𝒫, µ∈𝒞} ∫ l dP` subject to `∫ φ dP = µ`, has the same optimal value as
`min_{f₀∈ℝ, f∈ℋ} δ*_𝒞(f) + f₀` subject to `l(ξ) ≤ f₀ + f(ξ), ∀ ξ ∈ 𝒳` (12): strong duality holds.

**Formalization Note.** Standing hypotheses (Assumption 3.1, p. 3, and §2, p. 2): `𝒳` is a compact metric space with its
Borel σ-algebra (a compact `𝒳 ⊂ ℝᵈ` is an instance); the feature map `φ` is continuous (equivalently,
the kernel is continuous; not written in Assumption 3.1, but used by §D.2 through a universal, hence
continuous, kernel); `𝒞` is closed and convex; `l` is upper semicontinuous with values in `[−∞, ∞)`
and proper (not identically `−∞`, p. 2). The Slater clause "ri(𝒦_𝒞) ≠ ∅", which names no topology on
measures and is used in the proof only as "the primal problem has a non-empty solution set" (p. 15),
is read as `𝒦_𝒞 ≠ ∅`, which it implies under any reading. The printed "min" in (12) is read as an infimum: the proof only
produces `ε`-optimal dual solutions and the dual need not attain its value (the page's "min" is an
overstatement; no attainment is claimed here). Both values are extended reals; the equality includes
the case where they are `−∞`, which the paper's proof argues away in its first paragraph. -/
theorem proposition_A_1 {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : X → H) (hφ : Continuous φ) (C : Set H) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (l : X → EReal) (hl_usc : UpperSemicontinuous l)
    (hl_top : ∀ ξ, l ξ ≠ ⊤) (hl_proper : ∃ ξ, l ξ ≠ ⊥)
    (hK : (ambiguitySet φ C).Nonempty) :
    primalValue φ C l = dualValue φ C l := by sorry

end KernelDRO.Duality
