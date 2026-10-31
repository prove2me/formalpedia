-- Prove2me | Theorems.Thm_KallMayerSLP_GenConcave_gammaConcave_antitone
-- name    : KallMayerSLP.GenConcave.gammaConcave_antitone
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:28.037067+00:00
-- url     : https://prove2.me/theorems/b72ccb59-2da7-4ea5-bfb3-b664b55d8cc7
-- title:
--   $\gamma_2$-concavity implies $\gamma_1$-concavity for $\gamma_1<\gamma_2$, and every $\gamma$-concave function is quasi-concave
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R_+$.
--
--   1. If $f$ is $\gamma_2$-concave, then $f$ is $\gamma_1$-concave for every $\gamma_1<\gamma_2$ (with $\gamma_1,\gamma_2\in[-\infty,\infty]$).
--   2. If $f$ is $\gamma$-concave for some $\gamma\in[-\infty,\infty]$, then $f$ is quasi-concave: every upper level set $\{x\mid f(x)\ge t\}$ is convex.
--
--   This is the hierarchy of Figure 2.6: the classes of $\gamma$-concave functions shrink as $\gamma$ grows, and all of them consist of quasi-concave functions.
--
--   **Formalization Note** Exponents are extended reals; quasi-concavity is Mathlib's `QuasiconcaveOn ℝ Set.univ f`.
--
--   Differences from the source:
--   - encoding: $\gamma\in[-\infty,\infty]$ → `EReal`; reason: Lean convention, same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §2.5.1, p.124 (PDF 134)

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_IsGammaConcaveFun

namespace KallMayerSLP.GenConcave

/-- **Consequence of the monotonicity of the generalized means for `γ`-concave functions**
(Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §2.5.1, p. 124,
PDF p. 134): if `f` is `γ₂`-concave, then it is `γ₁`-concave for all `γ₁ < γ₂`. In
particular, if `f` is `γ`-concave for any `γ ∈ [−∞, ∞]` then `f` is quasi-concave.

**Formalization Note.** `f : ℝⁿ → ℝ` with `ℝⁿ = Fin n → ℝ`; exponents in `EReal`;
quasi-concavity is Mathlib's `QuasiconcaveOn ℝ Set.univ f` (every upper level set
`{x | t ≤ f x}` is convex). -/
theorem gammaConcave_antitone {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    (∀ γ₁ γ₂ : EReal, γ₁ < γ₂ → IsGammaConcaveFun γ₂ f → IsGammaConcaveFun γ₁ f) ∧
    (∀ γ : EReal, IsGammaConcaveFun γ f → QuasiconcaveOn ℝ Set.univ f) := by sorry

end KallMayerSLP.GenConcave
