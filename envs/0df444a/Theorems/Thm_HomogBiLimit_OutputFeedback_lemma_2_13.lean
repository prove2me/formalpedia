-- Prove2me | Theorems.Thm_HomogBiLimit_OutputFeedback_lemma_2_13
-- name    : HomogBiLimit.OutputFeedback.lemma_2_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:24.113973+00:00
-- url     : https://prove2.me/theorems/64e0db32-53c0-40ae-aa59-1b7689d6b5d5
-- title:
--   Lemma 2.13 — key technical lemma: $\eta-c\gamma<0$ off the origin for all large $c$
-- statement:
--   Let $\eta:\mathbb R^n\to\mathbb R$ and $\gamma:\mathbb R^n\to[0,\infty)$ be homogeneous in the bi-limit with the same weights $r_0,r_\infty$ and degrees $d_0,d_\infty$, with approximating functions $\eta_0,\eta_\infty$ and $\gamma_0,\gamma_\infty$. Assume
--   $$\{x\ne0:\gamma(x)=0\}\subseteq\{\eta<0\},\quad \{x\ne0:\gamma_0(x)=0\}\subseteq\{\eta_0<0\},\quad \{x\ne0:\gamma_\infty(x)=0\}\subseteq\{\eta_\infty<0\}.$$
--   Then there is a real number $c^*$ such that for all $c\ge c^*$ and all $x\in\mathbb R^n\setminus\{0\}$,
--   $$\eta(x)-c\,\gamma(x)<0,\qquad \eta_0(x)-c\,\gamma_0(x)<0,\qquad \eta_\infty(x)-c\,\gamma_\infty(x)<0 .$$
--
--   This is a global "completion of squares" without an explicit constant; it is the step that closes every Lyapunov argument of the paper, including the proof of Theorem 5.1.
-- source:
--   Andrieu, Praly, Astolfi, Homogeneous Approximation, Recursive Observer Design, and Output Feedback, arXiv:0903.0298v1, p. 6, Lemma 2.13, (2.4)

import Mathlib
import Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity
import Definitions.Def_HomogBiLimit_OutputFeedback_ChainSystems

namespace HomogBiLimit.OutputFeedback

/-- Lemma 2.13 (key technical lemma), p. 6. -/
theorem lemma_2_13 {n : ℕ} (η η₀ ηinf γ γ₀ γinf : (Fin n → ℝ) → ℝ)
    (r₀ rinf : Fin n → ℝ) (d₀ dinf : ℝ)
    (hη : IsHomogBiLimit η r₀ d₀ η₀ rinf dinf ηinf)
    (hγ : IsHomogBiLimit γ r₀ d₀ γ₀ rinf dinf γinf)
    (hγ_nonneg : ∀ x, 0 ≤ γ x)
    (h : ∀ x, x ≠ 0 → γ x = 0 → η x < 0)
    (h₀ : ∀ x, x ≠ 0 → γ₀ x = 0 → η₀ x < 0)
    (hinf : ∀ x, x ≠ 0 → γinf x = 0 → ηinf x < 0) :
    ∃ cstar : ℝ, ∀ c : ℝ, cstar ≤ c → ∀ x : Fin n → ℝ, x ≠ 0 →
      η x - c * γ x < 0 ∧ η₀ x - c * γ₀ x < 0 ∧ ηinf x - c * γinf x < 0 := by sorry

end HomogBiLimit.OutputFeedback
