-- Prove2me | Theorems.Thm_HopRamsey_lemma_2_ineq_sharp
-- name    : HopRamsey.lemma_2_ineq_sharp
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:45:03.228653+00:00
-- url     : https://prove2.me/theorems/b359e983-6814-4099-9fd7-33abb0da7234
-- title:
--   Inequality (#): $\frac{\Delta}{r_\ell-r_{\ell-1}}\ln\frac{2\mu_\ell}{\delta}\le 2^6L\log\mu_\ell$
-- statement:
--   Let $N=|V|\ge2$, $1\le\ell\le L$ and $\Delta>0$, with the parameters of Figure 2. Then
--
--   $$
--   \frac{\Delta}{r_\ell-r_{\ell-1}}\cdot\ln\frac{2\mu_\ell}{\delta}\le 2^6\cdot L\cdot\log\mu_\ell .
--   $$
--
--   This is the step (#) of the proof of Lemma 2: the expected contribution of a padded split in phase $\ell$ is at most $2^8L\log\mu_\ell\cdot d^{(h)}_G(u,v)$, which the induction absorbs into $g$.
--
--   Differences from the source:
--   - reading: the chain ∆/(r_ℓ−r_{ℓ−1})·ln(2µ_ℓ/δ) = … ≤ … ≤ 2^6·L·2^{L−ℓ} = 2^6·L·log µ_ℓ → its first and last terms: ∆/(r_ℓ−r_{ℓ−1})·ln(2µ_ℓ/δ) ≤ 2^6·L·log₂ µ_ℓ; reason: the intermediate terms are the proof of the inequality
--   - generalization: ∆ the scale of a call → any ∆ > 0; reason: the left side does not depend on ∆
--   - reading: the standing assumption |V| ≥ 2 of §4 ("recall |V| ≥ n ≥ 2", p.22) → hypothesis 2 ≤ P.N; reason: the section's standing assumption, restated; it excludes no instance of the inequality (for |V| ≤ 1, L = 0 and no ℓ with 1 ≤ ℓ ≤ L exists)
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), proof of Lemma 2, inequality (#), p.24 (PDF p.26)

import Mathlib
import Definitions.Def_HopRamsey_Fig2Params

open scoped ENNReal

namespace HopRamsey

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…),
Inequality (#), proof of Lemma 2, p.24 (PDF p.26): "∆/(r_ℓ − r_{ℓ−1}) · ln(2µ_ℓ/δ) =
1/(1/2^{L−ℓ+4} + 1/(8L)) · (ln(2µ_ℓ) + ln(1/δ)) ≤ 1/max{1/2^{L−ℓ+4}, 1/(8L)} · (2^{L−ℓ+1} + 2L)
≤ 2^4 · min{2^{L−ℓ}, L} · 2 · (2^{L−ℓ} + L) ≤ 2^6 · L · 2^{L−ℓ} = 2^6 · L · log µ_ℓ"

**Formalization Note.** The first and last terms of the chain, for `|V| ≥ 2`, `1 ≤ ℓ ≤ L` and
`∆ > 0`, with the parameters of Figure 2 (`log = log₂`, `ln` natural). -/
theorem lemma_2_ineq_sharp (P : Fig2Params) (hN : 2 ≤ P.N) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓL : ℓ ≤ P.L)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    Δ / (P.r Δ ℓ - P.r Δ (ℓ - 1)) * Real.log (2 * (P.mu ℓ : ℝ) / P.delta) ≤
      2 ^ 6 * P.L * Real.logb 2 (P.mu ℓ) := by sorry

end HopRamsey
