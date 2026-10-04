-- Prove2me | Theorems.Thm_MeanFieldOpt_ControlDuality_lemma_7_2_ab
-- name    : MeanFieldOpt.ControlDuality.lemma_7_2_ab
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:07:19.476673+00:00
-- url     : https://prove2.me/theorems/6fbfa44c-4cc5-409d-924e-10edde3ae212
-- title:
--   Lemma 7.2(a)–(b) — space derivatives of $\Phi_\gamma$ are continuous on $[0,1)\times\mathbb R$, and $C^1$ in time where $\gamma$ is constant
-- statement:
--   Let $\xi$ be a mixture that is not identically zero and let $\gamma\in\mathsf{SF}_+$, with Cole–Hopf solution $\Phi_\gamma$ of the Parisi PDE with terminal condition $\Phi_\gamma(1,x)=|x|$. Then:
--
--   1. for every $t\in[0,1)$, $x\mapsto\Phi_\gamma(t,x)$ is infinitely differentiable, and for every $j\ge0$ the derivative $\partial_x^j\Phi_\gamma$ is jointly continuous on $[0,1)\times\mathbb R$;
--   2. for every interval $[a,b)\subseteq[0,1)$ on which $\gamma$ is constant and every $j\ge0$, $\partial_x^j\Phi_\gamma$ has a time derivative $\partial_t\partial_x^j\Phi_\gamma$ (one-sided from the right at each $t\in[a,b)$) which is jointly continuous on $[a,b)\times\mathbb R$.
--
--   These regularity facts make $\Phi_\gamma$ a classical solution between the jump times of $\gamma$, which the verification argument for the control problem requires.
--
--   **Formalization Note** The hypothesis that $\xi$ is not identically zero (some $c_k\neq0$) is added: for $\xi\equiv0$ one has $\Phi_\gamma(t,x)=|x|$ for all $t$, whose derivative is discontinuous at $0$. The derivative in time is a right derivative, because $\gamma$ may jump at the left end $a$. Smoothness of $\Phi_\gamma(t,\cdot)$ is stated explicitly so that the iterated derivatives are true derivatives.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 35, Lemma 7.2 (a), (b)

import Mathlib
import Definitions.Def_MeanFieldOpt_ControlDuality_ColeHopf

open Set

namespace MeanFieldOpt.ControlDuality

/-- Lemma 7.2 (a), (b) (arXiv:2001.00904v1, p. 35), for a mixture that is not identically zero.
(a) For every `t ∈ [0, 1)`, `Φ_γ(t, ·)` is `C^∞`, and every space derivative `∂_x^j Φ_γ` is
jointly continuous on `[0, 1) × ℝ`.
(b) On every interval `[a, b) ⊆ [0, 1)` on which `γ` is constant, every `∂_x^j Φ_γ` has a
(right) time derivative `∂_t ∂_x^j Φ_γ` that is jointly continuous on `[a, b) × ℝ`. -/
theorem lemma_7_2_ab (ξ : Mixture) (hξ : ∃ k, ξ.c k ≠ 0) (d : SFData) :
    (∀ t ∈ Ico (0 : ℝ) 1, ∀ n : ℕ, ContDiff ℝ n (PhiSF ξ d t)) ∧
    (∀ j : ℕ, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv j (PhiSF ξ d p.1) p.2)
      (Ico (0 : ℝ) 1 ×ˢ univ)) ∧
    (∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → (∃ g : ℝ, ∀ s ∈ Ico a b, d.toFun s = g) →
      ∀ j : ℕ, ∃ D : ℝ → ℝ → ℝ,
        ContinuousOn (fun p : ℝ × ℝ => D p.1 p.2) (Ico a b ×ˢ univ) ∧
        ∀ t ∈ Ico a b, ∀ x : ℝ,
          HasDerivWithinAt (fun s => iteratedDeriv j (PhiSF ξ d s) x) (D t x) (Ici t) t) := by sorry

end MeanFieldOpt.ControlDuality
