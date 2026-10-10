-- Prove2me | Theorems.Thm_NAGFlow_Flow_remark_3_1
-- name    : NAGFlow.Flow.remark_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:35.464255+00:00
-- url     : https://prove2.me/theorems/1a55c9c4-dd11-443f-b7b9-7bf2245e900e
-- title:
--   Remark 3.1, p. 14 — with (54) relaxed to γ′ ≤ μ − γ, (63) becomes an inequality and (59) still holds
-- statement:
--   Let $V$ be a real Hilbert space, $f\in\mathcal S^1_\mu$, $x^*$ a global minimizer of $f$, and let $\gamma:[0,\infty)\to(0,\infty)$ be differentiable (right derivative at $0$) with
--   $$\gamma'(t)\le\mu-\gamma(t)\qquad\forall\,t\ge0$$
--   in place of the equation (54). Let $(x,v)\in C^1([0,\infty);V)^2$ be a classical solution of (56) $x'=v-x$, $\gamma v'=\mu(x-v)-\nabla f(x)$ with this $\gamma$, and $\mathcal L(t)=f(x)-f(x^*)+\frac{\gamma}{2}\|v-x^*\|^2$. Then for every $t\ge0$, $\mathcal L$ is differentiable at $t$ relative to $[0,\infty)$ and
--   $$\mathcal L'(t)\le\frac{\mu}{2}\|x-x^*\|^2-\langle\nabla f(x),x-x^*\rangle-\frac{\gamma}{2}\|v-x^*\|^2-\frac{\mu}{2}\|x'\|^2,$$
--   $$\mathcal L'(t)\le-\mathcal L(t)-\frac{\mu}{2}\|x'(t)\|^2 . \tag{59}$$
--
--   The remark gives freedom in the choice of the scaling factor; the discrete schemes of the later sections use this freedom.
--
--   **Formalization Note.** Positivity of $\gamma$ on $[0,\infty)$ is added: the paper's $\gamma$ is a positive scaling factor throughout (it divides $v'$ in (56)), and $\gamma'\le\mu-\gamma$ with $\gamma(0)>0$ alone does not keep it positive. The relaxed (61) is not stated separately; the inequality form of (63) and (59) are.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, Remark 3.1, p. 14

import Mathlib
import Definitions.Def_NAGFlow_Flow_Setting

namespace NAGFlow.Flow

open Set
open scoped InnerProductSpace

/-- Remark 3.1, p. 14. Relax (54) to `γ′ ≤ μ − γ`: let `γ` be any positive function on `[0, ∞)`,
differentiable there (right derivative `γ'` at `0`) with `γ′(t) ≤ μ − γ(t)`. Let `f ∈ S¹_μ`, `x*` a
global minimizer, and `(x, v)` a classical `C¹` solution of (56) with this `γ`. Then (63) becomes an
inequality, `ℒ′(t) ≤ μ/2 ‖x − x*‖² − ⟨∇f(x), x − x*⟩ − γ/2 ‖v − x*‖² − μ/2 ‖x′‖²`, and the estimate
(59) `ℒ′(t) ≤ −ℒ(t) − μ/2 ‖x′(t)‖²` still holds, for every `t ≥ 0`. -/
theorem remark_3_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ : ℝ) (hf : NAGFlow.PredCorr.IsS1 f gradf μ)
    (γ γ' : ℝ → ℝ) (hγpos : ∀ t, 0 ≤ t → 0 < γ t)
    (hγderiv : ∀ t, 0 ≤ t → HasDerivWithinAt γ (γ' t) (Ici 0) t)
    (hγle : ∀ t, 0 ≤ t → γ' t ≤ μ - γ t)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y) (x₀ v₀ : V) (x v : ℝ → V)
    (hsol : IsSys56 f gradf μ γ x₀ v₀ x v) (t : ℝ) (ht : 0 ≤ t) :
    ∃ dL : ℝ, HasDerivWithinAt (lyapFlow f xstar γ x v) dL (Ici 0) t ∧
      dL ≤ μ / 2 * ‖x t - xstar‖ ^ 2 - ⟪gradf (x t), x t - xstar⟫_ℝ
        - γ t / 2 * ‖v t - xstar‖ ^ 2 - μ / 2 * ‖dI x t‖ ^ 2 ∧
      dL ≤ -lyapFlow f xstar γ x v t - μ / 2 * ‖dI x t‖ ^ 2 := by sorry

end NAGFlow.Flow
