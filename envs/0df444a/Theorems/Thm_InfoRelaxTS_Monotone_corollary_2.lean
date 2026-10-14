-- Prove2me | Theorems.Thm_InfoRelaxTS_Monotone_corollary_2
-- name    : InfoRelaxTS.Monotone.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:20.518195+00:00
-- url     : https://prove2.me/theorems/84d7bc54-a5a8-46df-96d9-0b55124eb777
-- title:
--   Corollary 2, pp. 57–58 — 𝔼[max_i{(i−n)⁺X + C_i}] ≥ 𝔼[max_i{𝔼(X|ℋ)1{i ≥ n+1} + (i−n−1)⁺X + C_i}]
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $\mathcal H \subseteq \mathcal F$ a sub-$\sigma$-field, $X$ an integrable random variable and $C_0,\dots,C_T$ integrable $\mathcal H$-measurable random variables. Then for every $n \in \{0,1,\dots,T\}$,
--
--   $$\mathbb E\Big[\max_{0\le i\le T}\big\{(i-n)^+ X + C_i\big\}\Big] \ge \mathbb E\Big[\max_{0\le i\le T}\big\{\mathbb E(X\mid\mathcal H)\,\mathbf 1\{i \ge n+1\} + (i-n-1)^+ X + C_i\big\}\Big].$$
--
--   Replacing one copy of $X$ by its conditional expectation, in every option that uses at least $n+1$ copies, lowers the expected maximum. Applied arm by arm with $X = \hat\mu_{k,T-1}$, it gives $U_{k,n} \ge U_{k,n+1}$ (155).
--
--   **Formalization Note** The page's "real-valued random variables" $C_i$ are taken integrable (disclosed), and $\mathbb E|X| < \infty$ is inherited from Lemma 1, so both expectations are finite. The positive parts $(i-n)^+$ and $(i-n-1)^+$ are natural-number subtractions, which coincide with the positive part.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, pp. 57–58, Corollary 2, (142)

import Mathlib
import Definitions.Def_InfoRelaxTS_Monotone_Setting

namespace InfoRelaxTS.Monotone

open MeasureTheory ProbabilityTheory

/-- Corollary 2, pp. 57–58, (142): for `ℋ`-measurable integrable `C_0, …, C_T`, integrable `X` and
`n ∈ {0, …, T}`,
`𝔼[max_{0≤i≤T} {(i − n)⁺ X + C_i}] ≥ 𝔼[max_{0≤i≤T} {𝔼(X|ℋ)·1{i ≥ n+1} + (i − n − 1)⁺ X + C_i}]`.
The positive parts `(i − n)⁺`, `(i − n − 1)⁺` are natural-number subtractions. -/
theorem corollary_2 {Ω : Type*} {mH mΩ : MeasurableSpace Ω} (hmH : mH ≤ mΩ)
    (μ : @Measure Ω mΩ) [@IsProbabilityMeasure Ω mΩ μ]
    (T : ℕ) (C : Fin (T + 1) → Ω → ℝ) (hCmeas : ∀ i, Measurable[mH] (C i))
    (hCint : ∀ i, Integrable (C i) μ) (X : Ω → ℝ) (hX : Integrable X μ) (n : ℕ) (hn : n ≤ T) :
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (T + 1) =>
        (μ[X | mH]) ω * (if n + 1 ≤ (i : ℕ) then (1 : ℝ) else 0)
          + (((i : ℕ) - n - 1 : ℕ) : ℝ) * X ω + C i ω) ∂μ
      ≤ ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (T + 1) =>
        (((i : ℕ) - n : ℕ) : ℝ) * X ω + C i ω) ∂μ := by sorry

end InfoRelaxTS.Monotone
