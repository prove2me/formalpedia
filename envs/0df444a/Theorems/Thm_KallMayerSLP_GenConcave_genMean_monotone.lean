-- Prove2me | Theorems.Thm_KallMayerSLP_GenConcave_genMean_monotone
-- name    : KallMayerSLP.GenConcave.genMean_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:02.886003+00:00
-- url     : https://prove2.me/theorems/f59632bf-feec-4d8c-a7b0-2c4d6fe46537
-- title:
--   Generalized means increase with the exponent (corrected: strict only for $0<\lambda<1$)
-- statement:
--   The generalized means $\mathcal M_\gamma^\lambda$ are nondecreasing in the exponent $\gamma\in[-\infty,\infty]$:
--
--   1. for $\gamma_1<\gamma_2$, every $\lambda\in[0,1]$ and all $a,b\ge 0$,
--   $$
--   \mathcal M_{\gamma_1}^\lambda(a,b)\ \le\ \mathcal M_{\gamma_2}^\lambda(a,b);
--   $$
--   2. for $\gamma_1<\gamma_2$, $0<\lambda<1$ and $a,b>0$ with $a\neq b$, the inequality is strict.
--
--   This monotonicity orders the classes of generalized concave functions and measures: $\gamma$-concavity becomes weaker as $\gamma$ decreases, from constancy on the support ($\gamma=\infty$) through concavity and log-concavity down to quasi-concavity ($\gamma=-\infty$).
--
--   **Formalization Note** Exponents are extended reals (`EReal`).
--
--   Differences from the source:
--   - correction: strict inequality unless $a=b$ or $ab=0$, for every $\lambda\in[0,1]$ → strict inequality for $0<\lambda<1$, $a,b>0$, $a\neq b$; reason: at $\lambda=1$, $a=1$, $b=2$, $\gamma_1=0<\gamma_2=1$ both means equal $1$ (at $\lambda\in\{0,1\}$ every finite-exponent mean is $b$ or $a$)
--   - encoding: $\gamma\in\mathbb R\cup\{-\infty\}\cup\{\infty\}$ → `EReal`; reason: Lean convention, same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §2.5.1, p.123 (PDF 133), monotonicity of the generalized means (cited from Hardy, Littlewood and Pólya [112])

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_genMean

namespace KallMayerSLP.GenConcave

/-- **Monotonicity of the generalized means** (Kall & Mayer, *Stochastic Linear
Programming* (2005), Chapter 2, §2.5.1, p. 123, PDF p. 133; cited from Hardy, Littlewood
and Pólya [112]):
`γ₁ < γ₂ ⟹ M_{γ₁}^λ(a, b) ≤ M_{γ₂}^λ(a, b)` for all `a, b ≥ 0`, with the inequality strict
unless `a = b` or `ab = 0`.

**Formalization Note.** The non-strict clause is stated for every `λ ∈ [0, 1]`. The strict
clause is stated for `λ ∈ (0, 1)`: at `λ ∈ {0, 1}` every finite-exponent mean equals `b` or
`a`, so the printed strictness is false there (`λ = 1`, `a = 1`, `b = 2`, `γ₁ = 0 < γ₂ = 1`:
both means equal `1`). Exponents range over `EReal`. -/
theorem genMean_monotone :
    (∀ γ₁ γ₂ : EReal, γ₁ < γ₂ → ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      genMean γ₁ lam a b ≤ genMean γ₂ lam a b) ∧
    (∀ γ₁ γ₂ : EReal, γ₁ < γ₂ → ∀ lam ∈ Set.Ioo (0 : ℝ) 1, ∀ a b : ℝ, 0 < a → 0 < b → a ≠ b →
      genMean γ₁ lam a b < genMean γ₂ lam a b) := by sorry

end KallMayerSLP.GenConcave
