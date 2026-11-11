-- Prove2me | Theorems.Thm_FrechetNearLinear_Main_lemma_7_1
-- name    : FrechetNearLinear.Main.lemma_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:35:45.964596+00:00
-- url     : https://prove2.me/theorems/5406f8b7-3344-400e-8bf7-270f59195ce1
-- title:
--   Lemma 7.1 — parameters K, θ, T: β_{i−1,T} ≤ θ < α_{i−1}, α_K < ε̄/2, δ_K < ε̄/4, 2D_K ≤ exp(exp(O(ε⁻¹ log(2/ε))))
-- statement:
--   For $\varepsilon>0$ let $\bar\varepsilon=\min\{\varepsilon,1\}$, $K=\lceil6/\bar\varepsilon\rceil$, $\theta=1/K$, $T=\lceil(4/\theta)\log(16/\theta)\rceil$, and define $(\alpha_i,\delta_i;D_i)$ by (7.1) from $(\alpha_0,\delta_0;D_0)=(1,0;9)$. Let $\beta_{j,t}$ be the query exponent of (5.1) with $\delta=\delta_j$. Then
--   $$\beta_{i-1,T}\le\theta<\alpha_{i-1}\quad(1\le i\le K),\qquad \alpha_K<\frac{\bar\varepsilon}{2},\qquad\delta_K<\frac{\bar\varepsilon}{4},$$
--   and there is a universal constant $c$ such that for every $0<\varepsilon\le1$
--   $$2D_K\le\exp\!\big(\exp\big(c\,\varepsilon^{-1}\log(2/\varepsilon)\big)\big).$$
--
--   These parameters make Theorem 6.2 applicable in each of the $K$ outer rounds, and $f(1/\varepsilon)=2D_K$ is the approximation factor of Theorem 1.1.
--
--   Differences from the source:
--   - reading: "$2D_K\le\exp(\exp(O(\varepsilon^{-1}\log(2/\varepsilon))))$ for $0<\varepsilon\le1$" → $\exists c,\ \forall\varepsilon\in(0,1],\ 2D_K\le\exp(\exp(c\,\varepsilon^{-1}\log(2/\varepsilon)))$; reason: the $O(\cdot)$ is a constant independent of $\varepsilon$
--   - reading: "log" → the natural logarithm `Real.log`; reason: the proof uses $(1+\delta_j)^{-T}\le e^{-T\theta/4}$
-- source:
--   Huang, Wang, Zhang, Constant Approximation of Fréchet Distance in Near-Linear Time, STOC 2027 submission (manuscript sha256 08be7e65…dd2d), p. 33, Lemma 7.1

import Mathlib
import Definitions.Def_FrechetNearLinear_Main_Recurrences

namespace FrechetNearLinear.Main

/-- Lemma 7.1 (Parameters), p. 33. With `ε̄, K, θ, T` and `(αᵢ, δᵢ; Dᵢ)` of (7.1) and `β_{j,t}`
the query exponent of (5.1) for `δ = δ_j`: for every `ε > 0`, `β_{i-1,T} ≤ θ < α_{i-1}` for
`1 ≤ i ≤ K`, `α_K < ε̄/2` and `δ_K < ε̄/4`; and there is a universal constant `c` with
`2 D_K ≤ exp(exp(c · ε⁻¹ log(2/ε)))` for every `0 < ε ≤ 1`. -/
theorem lemma_7_1 :
    (∀ ε : ℝ, 0 < ε →
      (∀ i : ℕ, 1 ≤ i → i ≤ numRounds ε →
        queryExp (roundDelta ε (i - 1)) (innerDepth ε) ≤ theta ε ∧
          theta ε < roundAlpha ε (i - 1)) ∧
      roundAlpha ε (numRounds ε) < epsBar ε / 2 ∧
      roundDelta ε (numRounds ε) < epsBar ε / 4) ∧
    (∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      2 * roundD ε (numRounds ε) ≤ Real.exp (Real.exp (c * (ε⁻¹ * Real.log (2 / ε))))) := by sorry

end FrechetNearLinear.Main
