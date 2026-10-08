-- Prove2me | Theorems.Thm_KernelDRO_Duality_tau_neg_dual_feasible
-- name    : KernelDRO.Duality.tau_neg_dual_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:52.917592+00:00
-- url     : https://prove2.me/theorems/c52c3da0-d110-409f-9784-dc36e98690b6
-- title:
--   Proof of Prop. A.1, p. 15 — $\tau<0$, and $(f_0,f)/(-\tau)$ is dual feasible with objective $\le t+\epsilon$
-- statement:
--   Under the standing hypotheses below, let the primal value of (11) be a real number $t$, let $\epsilon>0$, and let $(f_0,f,\tau)\in\mathbb R\times\mathcal H\times\mathbb R$ satisfy the two inequalities (14):
--   $$f_0+\langle f,\mu\rangle_{\mathcal H}+\tau(t+\epsilon)<0\ \ \forall\mu\in\mathcal C,\qquad f_0+\langle f,\mu_P\rangle_{\mathcal H}+\tau\int l\,dP\ge0\ \ \forall P\in\mathcal P .$$
--   Then
--
--   1. $\tau<0$;
--   2. the rescaled pair $\big(f_0/(-\tau),\,f/(-\tau)\big)$ is feasible for the dual (12): $l(\xi)\le \frac{f_0}{-\tau}+\big\langle\frac{f}{-\tau},\varphi(\xi)\big\rangle_{\mathcal H}$ for all $\xi\in\mathcal X$;
--   3. its dual objective satisfies $\frac{f_0}{-\tau}+\delta^*_{\mathcal C}\big(\frac{f}{-\tau}\big)\le t+\epsilon$.
--
--   The paper's "without loss of generality, we let $\tau=-1$" is this rescaling.
--
--   **Standing hypotheses.** $\mathcal X$ is a compact metric space with its Borel $\sigma$-algebra and $\mathcal P$ is the set of Borel probability measures on $\mathcal X$. $\mathcal H$ is a real Hilbert space with a continuous feature map $\varphi:\mathcal X\to\mathcal H$, and $f\in\mathcal H$ acts on $\mathcal X$ by the reproducing property $f(\xi)=\langle f,\varphi(\xi)\rangle_{\mathcal H}$. The set $\mathcal C\subseteq\mathcal H$ is closed and convex, the ambiguity set $\mathcal K_{\mathcal C}=\{P\in\mathcal P:\mu_P\in\mathcal C\}$ with $\mu_P=\int\varphi\,dP$ is nonempty, and the loss $l:\mathcal X\to[-\infty,\infty)$ is upper semicontinuous and proper (not identically $-\infty$).
--
--   **Formalization Note** $\int l\,dP$ is the published extended-real expectation `erealExpectation`, which for an upper semicontinuous loss on a compact space is the usual $\int l\,dP\in[-\infty,\infty)$. The Slater clause $\mathrm{ri}(\mathcal K_{\mathcal C})\neq\emptyset$ of Assumption 3.1 is read as $\mathcal K_{\mathcal C}\neq\emptyset$, the only use the proof makes of it (p. 15). Continuity of $\varphi$ (equivalently of the kernel) is not written in Assumption 3.1 but is used by Appendix D through a universal, hence continuous, kernel. A compact $\mathcal X\subset\mathbb R^d$ is an instance of the compact metric space.
-- source:
--   Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, unnumbered, proof of Proposition A.1, p. 15

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_KernelDRO_Duality_Setting

open MeasureTheory

namespace KernelDRO.Duality

open WassersteinDRO.Duality

/-- **`τ < 0` and dual feasibility** (Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally
Robust Optimization, arXiv:2006.06981v3, unnumbered, proof of Proposition A.1, p. 15): "Using this and
the first inequality of (14), we obtain τ < 0. Without loss of generality, we let τ = −1." Let `t` be
the finite primal value, `ε > 0`, and let `(f₀, f, τ)` satisfy the two inequalities (14). Then
`τ < 0`; the rescaled pair `(f₀ / (−τ), f / (−τ))` is feasible for the dual (12), i.e.
`l(ξ) ≤ f₀/(−τ) + ⟨f/(−τ), φ(ξ)⟩` for all `ξ`; and its dual objective satisfies
`f₀/(−τ) + δ*_𝒞(f/(−τ)) ≤ t + ε`.

**Formalization Note.** Standing hypotheses (Assumption 3.1, p. 3, and §2, p. 2): `𝒳` is a compact metric space with its
Borel σ-algebra (a compact `𝒳 ⊂ ℝᵈ` is an instance); the feature map `φ` is continuous (equivalently,
the kernel is continuous; not written in Assumption 3.1, but used by §D.2 through a universal, hence
continuous, kernel); `𝒞` is closed and convex; `l` is upper semicontinuous with values in `[−∞, ∞)`
and proper (not identically `−∞`, p. 2). The Slater clause "ri(𝒦_𝒞) ≠ ∅", which names no topology on
measures and is used in the proof only as "the primal problem has a non-empty solution set" (p. 15),
is read as `𝒦_𝒞 ≠ ∅`, which it implies under any reading. The paper's normalization "τ = −1" is the division by `−τ > 0`,
stated explicitly here. The inequalities (14) are taken in the form of `separation_14`. -/
theorem tau_neg_dual_feasible {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : X → H) (hφ : Continuous φ) (C : Set H) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (l : X → EReal) (hl_usc : UpperSemicontinuous l)
    (hl_top : ∀ ξ, l ξ ≠ ⊤) (hl_proper : ∃ ξ, l ξ ≠ ⊥)
    (hK : (ambiguitySet φ C).Nonempty) (t : ℝ) (ht : primalValue φ C l = (t : EReal)) (ε : ℝ)
    (hε : 0 < ε) (f₀ : ℝ) (f : H) (τ : ℝ)
    (h14_1 : ∀ μ ∈ C, f₀ + inner ℝ f μ + τ * (t + ε) < 0)
    (h14_2 : ∀ P : ProbabilityMeasure X,
      0 ≤ ((f₀ + inner ℝ f (meanEmbedding φ P) : ℝ) : EReal) +
        (τ : EReal) * erealExpectation (P : Measure X) l) :
    τ < 0 ∧ IsDualFeasible φ l (f₀ / (-τ)) ((-τ)⁻¹ • f) ∧
      ((f₀ / (-τ) : ℝ) : EReal) + supportFun C ((-τ)⁻¹ • f) ≤ ((t + ε : ℝ) : EReal) := by sorry

end KernelDRO.Duality
