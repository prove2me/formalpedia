-- Prove2me | Theorems.Thm_KallMayerSLP_GenConcave_theorem_2_10
-- name    : KallMayerSLP.GenConcave.theorem_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:42.687307+00:00
-- url     : https://prove2.me/theorems/25edbd15-0d0f-4561-a8f2-89f3941ac5fe
-- title:
--   Theorem 2.10 — jointly quasi-concave constraints and a $\gamma$-concave law give a $\gamma$-concave probability function
-- statement:
--   Let $g_i:\mathbb R^n\times\mathbb R^r\to\mathbb R$, $i=1,\dots,m$, and consider the probability function
--
--   $$
--   M(x)=\mathbb P_\xi\{\,g_i(x,\xi)\ge 0,\ i=1,\dots,m\,\}.
--   $$
--
--   Assume that
--
--   1. each $g_i$ is quasi-concave jointly in both arguments $(x,\xi)$;
--   2. $g=(g_1,\dots,g_m)$ is continuous;
--   3. $\xi$ has a $\gamma$-concave probability distribution.
--
--   Then $M$ is a $\gamma$-concave function on $\mathbb R^n$.
--
--   This extends Prékopa's log-concave result to $\gamma$-concave laws and covers, for instance, the log-normal distribution function via $g_i(x,\xi)=x_i-e^{\xi_i}$.
--
--   **Formalization Note** $\mathbb R^n$ and $\mathbb R^r$ are `Fin n → ℝ` and `Fin r → ℝ`; joint quasi-concavity and continuity are stated for each $g_i$ as a function of the pair $(x,\xi)$. The law of $\xi$ is a measure $\mu$ on $\mathbb R^r$.
--
--   Differences from the source:
--   - encoding: components indexed $i=1,\dots,s$ in (2.65) and $i=1,\dots,m$ in the theorem, $\xi\in\mathbb R^r$ in (2.65) and $\mathbb R^s$ in the proof → $i\in\{1,\dots,m\}$, $\xi\in\mathbb R^r$; reason: one index set and one dimension; same instances
--   - encoding: law $\mathbb P_\xi$ → a measure $\mu$ on $\mathbb R^r$; reason: every probability measure is a law, same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Theorem 2.10, p.133 (PDF 143); probability function (2.65), p.132 (PDF 142)

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_IsGammaConcaveFun
import Definitions.Def_KallMayerSLP_GenConcave_IsGammaConcaveMeasure

open MeasureTheory

namespace KallMayerSLP.GenConcave

/-- **Theorem 2.10** (Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2,
Theorem 2.10, p. 133, PDF p. 143, for the probability function (2.65), p. 132, PDF p. 142).
Let `M(x) = ℙ_ξ{g_i(x, ξ) ≥ 0, i = 1, …, m}` with `g_i : ℝⁿ × ℝ^r → ℝ`. Let the `g_i` be
quasi-concave functions, that is, jointly quasi-concave in both arguments, and let `g` be
continuous. Assume further that `ξ` has a `γ`-concave probability distribution. Then
`M(x)` is a `γ`-concave function.

**Formalization Note.** The book indexes the components `i = 1, …, s` in (2.65) and
`i = 1, …, m` in the theorem (and writes `ℝ^s` for the space of `ξ` in the proof); here the
components are `g i`, `i : Fin m`, and `ξ` lives in `ℝ^r = Fin r → ℝ` as in (2.65). Joint
quasi-concavity and continuity are stated for each `g_i` as a function of the pair
`(x, ξ) ∈ ℝⁿ × ℝ^r` (continuity of `g = (g_1, …, g_m)` is continuity of each component).
The law of `ξ` is the measure `μ`; `M(x)` is a real number. -/
theorem theorem_2_10 {n r m : ℕ} (g : Fin m → (Fin n → ℝ) → (Fin r → ℝ) → ℝ)
    (hqc : ∀ i, QuasiconcaveOn ℝ Set.univ
      (fun p : (Fin n → ℝ) × (Fin r → ℝ) => g i p.1 p.2))
    (hcont : ∀ i, Continuous (fun p : (Fin n → ℝ) × (Fin r → ℝ) => g i p.1 p.2))
    (γ : EReal) (μ : Measure (Fin r → ℝ)) (hμ : IsGammaConcaveMeasure γ μ) :
    IsGammaConcaveFun γ (fun x : Fin n → ℝ => (μ {ξ | ∀ i, 0 ≤ g i x ξ}).toReal) := by sorry

end KallMayerSLP.GenConcave
