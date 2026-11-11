-- Prove2me | Theorems.Thm_FrechetNearLinear_Main_lemma_5_10
-- name    : FrechetNearLinear.Main.lemma_5_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:35:48.908008+00:00
-- url     : https://prove2.me/theorems/57092b35-41c4-4a15-90b9-54498a431412
-- title:
--   Lemma 5.10 — closed form of the query exponents; β_t > δ and β_t decreases to δ
-- statement:
--   Let $0\le\delta<1$ and let $\beta_t$ be given by (5.1): $\beta_0=1$, $\beta_{t+1}=\beta_t(1+\delta)/(1+\beta_t)$. Then $\beta_t=1/(t+1)$ if $\delta=0$, and
--   $$\beta_t=\frac{\delta}{1-(1-\delta)(1+\delta)^{-t}}\qquad\text{if }0<\delta<1.$$
--   In both cases $\beta_t>\delta$ for every $t$, and $\beta_t$ decreases strictly to $\delta$.
--
--   The exponents $\beta_t$ govern the running time $\tilde O((p+q)\min\{p,q\}^{\beta_t})$ of the depth-$t$ general query (Theorem 5.4); the lemma shows that deeper inner recursion approaches the self-query excess $\delta$.
--
--   Differences from the source:
--   - reading: "$\beta_t\downarrow\delta$" → `StrictAnti β` and `Tendsto β atTop (𝓝 δ)`; reason: the strictly decreasing reading is the stronger one, and it holds
-- source:
--   Huang, Wang, Zhang, Constant Approximation of Fréchet Distance in Near-Linear Time, STOC 2027 submission (manuscript sha256 08be7e65…dd2d), p. 28, Lemma 5.10

import Mathlib
import Definitions.Def_FrechetNearLinear_Main_Recurrences

open Filter Topology

namespace FrechetNearLinear.Main

/-- Lemma 5.10 (Query exponents), p. 28. For `β_t` of (5.1) with `0 ≤ δ < 1`:
`β_t = 1 / (t + 1)` if `δ = 0`, `β_t = δ / (1 - (1 - δ)(1 + δ)^{-t})` if `0 < δ < 1`; in both
cases `β_t > δ` and `β_t` decreases strictly to `δ`. -/
theorem lemma_5_10 (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (δ = 0 → ∀ t : ℕ, queryExp δ t = 1 / ((t : ℝ) + 1)) ∧
    (0 < δ → ∀ t : ℕ, queryExp δ t = δ / (1 - (1 - δ) * ((1 + δ) ^ t)⁻¹)) ∧
    (∀ t : ℕ, δ < queryExp δ t) ∧
    StrictAnti (queryExp δ) ∧
    Tendsto (queryExp δ) atTop (𝓝 δ) := by sorry

end FrechetNearLinear.Main
