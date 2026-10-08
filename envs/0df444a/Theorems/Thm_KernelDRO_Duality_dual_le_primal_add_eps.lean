-- Prove2me | Theorems.Thm_KernelDRO_Duality_dual_le_primal_add_eps
-- name    : KernelDRO.Duality.dual_le_primal_add_eps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:43.473064+00:00
-- url     : https://prove2.me/theorems/cf4adcdf-7bbe-43e1-85cd-13ce4393d008
-- title:
--   Proof of Prop. A.1, p. 15 — $\mathrm{(D)}\le\mathrm{(P)}+\epsilon$
-- statement:
--   Under the standing hypotheses below, if the primal value $t$ of (11) is a real number, then for every $\epsilon>0$ the dual value of (12) satisfies
--   $$\inf\Big\{f_0+\delta^*_{\mathcal C}(f):\ l\le f_0+f\text{ on }\mathcal X\Big\}\ \le\ t+\epsilon .$$
--   Together with weak duality this gives strong duality when the primal value is finite.
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

/-- **`(D) ≤ (P) + ε`** (Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust
Optimization, arXiv:2006.06981v3, unnumbered, proof of Proposition A.1, p. 15): "By the first
inequality of (14), f₀ + sup_{µ∈𝒞}⟨f, µ⟩_ℋ ≤ t + ε, ∀ε > 0, where the left-hand side is precisely the
dual objective in (12). This implies (D) ≤ (P) + ε." If the primal value `t` of (11) is finite, then
the dual value of (12) is at most `t + ε` for every `ε > 0`.

**Formalization Note.** Standing hypotheses (Assumption 3.1, p. 3, and §2, p. 2): `𝒳` is a compact metric space with its
Borel σ-algebra (a compact `𝒳 ⊂ ℝᵈ` is an instance); the feature map `φ` is continuous (equivalently,
the kernel is continuous; not written in Assumption 3.1, but used by §D.2 through a universal, hence
continuous, kernel); `𝒞` is closed and convex; `l` is upper semicontinuous with values in `[−∞, ∞)`
and proper (not identically `−∞`, p. 2). The Slater clause "ri(𝒦_𝒞) ≠ ∅", which names no topology on
measures and is used in the proof only as "the primal problem has a non-empty solution set" (p. 15),
is read as `𝒦_𝒞 ≠ ∅`, which it implies under any reading. The dual value is the infimum (not the printed "min") of (12). -/
theorem dual_le_primal_add_eps {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : X → H) (hφ : Continuous φ) (C : Set H) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (l : X → EReal) (hl_usc : UpperSemicontinuous l)
    (hl_top : ∀ ξ, l ξ ≠ ⊤) (hl_proper : ∃ ξ, l ξ ≠ ⊥)
    (hK : (ambiguitySet φ C).Nonempty) (t : ℝ) (ht : primalValue φ C l = (t : EReal)) (ε : ℝ)
    (hε : 0 < ε) :
    dualValue φ C l ≤ ((t + ε : ℝ) : EReal) := by sorry

end KernelDRO.Duality
