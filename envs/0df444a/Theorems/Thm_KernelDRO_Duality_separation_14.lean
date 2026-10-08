-- Prove2me | Theorems.Thm_KernelDRO_Duality_separation_14
-- name    : KernelDRO.Duality.separation_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:42.145335+00:00
-- url     : https://prove2.me/theorems/622b6c4e-6902-4c4f-8ea7-b39be6a5779b
-- title:
--   (14), p. 15 — strict separation of the cone $A$ and $B_\epsilon$
-- statement:
--   Under the standing hypotheses below, suppose the primal value of (11) is a real number $t$, and let $\epsilon>0$. Then there exist $f_0\in\mathbb R$, $f\in\mathcal H$ and $\tau\in\mathbb R$ such that
--   $$f_0+\langle f,\mu\rangle_{\mathcal H}+\tau(t+\epsilon)<0\quad\forall\mu\in\mathcal C,$$
--   $$f_0+\Big\langle f,\int\varphi\,dP\Big\rangle_{\mathcal H}+\tau\int l\,dP\ \ge\ 0\quad\forall P\in\mathcal P .$$
--   These are the inequalities (14) obtained from a hyperplane strictly separating the cone $A=\{(\int1\,dP,\int\varphi\,dP,\int l\,dP):P\in\mathrm{co}(\mathcal P)\}$ from the disjoint set $B_\epsilon=\{(1,\mu,t+\epsilon):\mu\in\mathcal C\}$ in $\mathbb R\times\mathcal H\times\mathbb R$.
--
--   **Standing hypotheses.** $\mathcal X$ is a compact metric space with its Borel $\sigma$-algebra and $\mathcal P$ is the set of Borel probability measures on $\mathcal X$. $\mathcal H$ is a real Hilbert space with a continuous feature map $\varphi:\mathcal X\to\mathcal H$, and $f\in\mathcal H$ acts on $\mathcal X$ by the reproducing property $f(\xi)=\langle f,\varphi(\xi)\rangle_{\mathcal H}$. The set $\mathcal C\subseteq\mathcal H$ is closed and convex, the ambiguity set $\mathcal K_{\mathcal C}=\{P\in\mathcal P:\mu_P\in\mathcal C\}$ with $\mu_P=\int\varphi\,dP$ is nonempty, and the loss $l:\mathcal X\to[-\infty,\infty)$ is upper semicontinuous and proper (not identically $-\infty$).
--
--   **Formalization Note** $\int l\,dP$ is the published extended-real expectation `erealExpectation`, which for an upper semicontinuous loss on a compact space is the usual $\int l\,dP\in[-\infty,\infty)$. The Slater clause $\mathrm{ri}(\mathcal K_{\mathcal C})\neq\emptyset$ of Assumption 3.1 is read as $\mathcal K_{\mathcal C}\neq\emptyset$, the only use the proof makes of it (p. 15). Continuity of $\varphi$ (equivalently of the kernel) is not written in Assumption 3.1 but is used by Appendix D through a universal, hence continuous, kernel. A compact $\mathcal X\subset\mathbb R^d$ is an instance of the compact metric space. The second inequality is stated for probability measures rather than for the cone $\mathrm{co}(\mathcal P)$; both sides scale with $P$, so it is the same condition. It is an extended-real inequality: $\int l\,dP$ may be $-\infty$, and $\tau\int l\,dP$ is the extended-real product.
-- source:
--   Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, unnumbered, proof of Proposition A.1, (14), p. 15

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_KernelDRO_Duality_Setting

open MeasureTheory

namespace KernelDRO.Duality

open WassersteinDRO.Duality

/-- **The separation (14)** (Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust
Optimization, arXiv:2006.06981v3, unnumbered, proof of Proposition A.1, (14), p. 15). Let `t = (P)`
be the (finite) optimal value of the primal (11) and `ε > 0`. The cone
`A = {(∫ 1 dP, ∫ φ dP, ∫ l dP) : P ∈ co(𝒫)}` and the set `B_ε = {(1, µ, t + ε) : µ ∈ 𝒞}` are disjoint
and are strictly separated by a hyperplane `(f₀, f, τ) ∈ ℝ × ℋ × ℝ`, which yields
`f₀ + ⟨f, µ⟩_ℋ + τ(t + ε) < 0` for all `µ ∈ 𝒞` and
`f₀ ∫ 1 dP + ⟨f, ∫ φ dP⟩_ℋ + τ ∫ l dP ≥ 0` for all `P ∈ co(𝒫)`.

**Formalization Note.** Standing hypotheses (Assumption 3.1, p. 3, and §2, p. 2): `𝒳` is a compact metric space with its
Borel σ-algebra (a compact `𝒳 ⊂ ℝᵈ` is an instance); the feature map `φ` is continuous (equivalently,
the kernel is continuous; not written in Assumption 3.1, but used by §D.2 through a universal, hence
continuous, kernel); `𝒞` is closed and convex; `l` is upper semicontinuous with values in `[−∞, ∞)`
and proper (not identically `−∞`, p. 2). The Slater clause "ri(𝒦_𝒞) ≠ ∅", which names no topology on
measures and is used in the proof only as "the primal problem has a non-empty solution set" (p. 15),
is read as `𝒦_𝒞 ≠ ∅`, which it implies under any reading. The value `t` is a real number with `primalValue φ C l = t`. The
second inequality is stated for probability measures: both sides scale by `c ≥ 0` under `P ↦ cP`, so
this is the same as the paper's `P ∈ co(𝒫)`. It is stated in `EReal` with `∫ l dP = erealExpectation`,
which may be `−∞`; the product `τ · ∫ l dP` is the `EReal` product (for `τ < 0` and `∫ l dP = −∞` it is
`+∞`), and it is added to the real number `f₀ + ⟨f, µ_P⟩`, so `⊤ + ⊥` never arises. The disjointness
`A ∩ B_ε = ∅` asserted on the page is the reason the separation exists and is not stated separately. -/
theorem separation_14 {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : X → H) (hφ : Continuous φ) (C : Set H) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (l : X → EReal) (hl_usc : UpperSemicontinuous l)
    (hl_top : ∀ ξ, l ξ ≠ ⊤) (hl_proper : ∃ ξ, l ξ ≠ ⊥)
    (hK : (ambiguitySet φ C).Nonempty) (t : ℝ) (ht : primalValue φ C l = (t : EReal)) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ (f₀ : ℝ) (f : H) (τ : ℝ),
      (∀ μ ∈ C, f₀ + inner ℝ f μ + τ * (t + ε) < 0) ∧
      ∀ P : ProbabilityMeasure X,
        0 ≤ ((f₀ + inner ℝ f (meanEmbedding φ P) : ℝ) : EReal) +
          (τ : EReal) * erealExpectation (P : Measure X) l := by sorry

end KernelDRO.Duality
