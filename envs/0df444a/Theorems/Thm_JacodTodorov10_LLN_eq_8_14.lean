-- Prove2me | Theorems.Thm_JacodTodorov10_LLN_eq_8_14
-- name    : JacodTodorov10.LLN.eq_8_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:20:44.033534+00:00
-- url     : https://prove2.me/theorems/e94b3f59-fd84-4fe1-92c8-060e8527959e
-- title:
--   (8.14) — E(ĉ(kₙ)ᵢ | 𝓕_{iΔₙ}) ≤ K, with K uniform
-- statement:
--   Assume (H-$r$), (K-$v$) and the localized bound (8.3) with constant $C$ and functions $\gamma,\widehat\gamma$. There is a constant $K$, depending only on $C,r,v,\lambda,\gamma,\widehat\gamma$, such that for every mesh $\Delta\in(0,1]$, cutoff $u>0$, window $k\ge1$ and nonrandom integer $i\ge1$, the local volatility estimator
--   $$\widehat c(k)_i=\frac1{k\Delta}\sum_{j=1}^{k}|\Delta_{i+j}X|^2\,1_{\{|\Delta_{i+j}X|\le u\}}$$
--   is integrable and
--   $$\mathbb E\big(\widehat c(k)_i\,\big|\,\mathcal F_{i\Delta}\big)\le K\qquad\text{a.s.}$$
--
--   The local estimators are thus bounded in conditional mean, uniformly in the sampling parameters; this controls the factor $1+\widehat c(k_n)_{i-k_n-1}+\widehat c(k_n)_i$ in the remainder of the proof of Theorem 3.1.
--
--   **Formalization Note** As in (8.11), $K$ comes before the probability space, the model and $(\Delta,u,k)$, and $\Delta\le1$. Integrability is part of the conclusion.
-- source:
--   Jacod, Todorov, Do price and volatility jump together?, arXiv:1010.4990v1 (Ann. Appl. Probab. 20 (2010)), §8.2, step 3, (8.14), p. 28

import Mathlib
import Definitions.Def_JacodTodorov10_LLN_Local

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace JacodTodorov10.LLN

/-- **(8.14)** of Jacod–Todorov, *Do price and volatility jump together?*, arXiv:1010.4990v1
(Ann. Appl. Probab. 20 (2010)), §8.2, step 3, p. 28: under (H-r), (K-v) and the localized bound
(8.3) with constant `C`, there is a constant `K`, depending only on `C`, `r`, `v`, `λ`, `γ`, `γ̂`,
such that for every mesh `Δ ∈ (0, 1]`, cutoff `u > 0`, window `k ≥ 1` and nonrandom `i ≥ 1`, the local
volatility estimator `ĉ(k)_i` of (3.4) is integrable and `E(ĉ(k)_i | 𝓕_{iΔ}) ≤ K`.

Formalization Note: the constant is chosen before the probability space, the model and the
parameters `Δ`, `u`, `k`, so it is uniform over them, as in the paper (p. 25). The mesh is
restricted to `Δ ≤ 1` as in (8.11) (the paper's regime `Δ_n → 0`). The integrability of
`ĉ(k)_i` is part of the conclusion, so the conditional expectation is not a junk value. -/
theorem eq_8_14 {E : Type*} [MeasurableSpace E] (lam : Measure E) [SigmaFinite lam]
    (r v C : ℝ) (γ γhat : E → ℝ) :
    ∃ K : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : Data Ω E) (Γ : ℝ≥0 → Ω → ℝ),
      IsModel 𝓕 P lam M → HAssume 𝓕 P lam r M → KAssume 𝓕 P lam v M →
      Bdd83 lam M r v C Γ γ γhat →
      ∀ Δ u : ℝ, 0 < Δ → Δ ≤ 1 → 0 < u → ∀ k : ℕ, 1 ≤ k → ∀ i : ℕ, 1 ≤ i →
        Integrable (chat Δ u k M.X i) P ∧
        P[chat Δ u k M.X i | 𝓕 (Real.toNNReal ((i : ℝ) * Δ))] ≤ᵐ[P] fun _ => K := by sorry

end JacodTodorov10.LLN
