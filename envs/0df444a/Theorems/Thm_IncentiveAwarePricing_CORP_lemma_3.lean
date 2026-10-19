-- Prove2me | Theorems.Thm_IncentiveAwarePricing_CORP_lemma_3
-- name    : IncentiveAwarePricing.CORP.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:57.563715+00:00
-- url     : https://prove2.me/theorems/e78c27d1-6818-497d-a52d-9100713f8844
-- title:
--   Lemma 3, p. 57 — (v⁻ − b⁻)⁺ ≤ max_i s_i(1 − q_i) and, when another buyer wins, (b⁺_{−i} − v⁺_{−i})⁺ ≤ max_{j≠i} o_j q_j
-- statement:
--   Consider one lazy second-price auction with $N\ge2$ buyers, valuations $v\in\mathbb R^N$, bids $b\in\mathbb R^N$, reserves $r\in\mathbb R^N$ and allocation $q\in\{0,1\}^N$. Write $v^-$ and $b^-$ for the second highest valuation and bid, $b^+_{-i}=\max_{j\ne i}b_j$, $v^+_{-i}=\max_{j\ne i}v_j$, and let $s_i=(v_i-b_i)^+$ (shading) and $o_i=(b_i-v_i)^+$ (overbidding). Then
--   $$(v^--b^-)^+\le\max_{i}\,s_i(1-q_i), \tag{44}$$
--   and for every buyer $i$ with $q_i=0$ such that some other buyer $j\neq i$ gets the item,
--   $$(b^+_{-i}-v^+_{-i})^+\le\max_{j\ne i}\,o_jq_j. \tag{45}$$
--
--   These inequalities control how much untruthful bidding can lower the second price, and raise the competing bid that a losing buyer faces.
--
--   **Formalization Note** The second highest entry of a vector $w$ is $\max_{i\neq j}\min\{w_i,w_j\}$, which is well defined under ties. (45) is stated with the added hypothesis that some buyer $j\ne i$ gets the item: as printed it fails when nobody wins, e.g. $N=2$, $i=1$, $b_2=v_2+5<r_2$, where the left side is $5$ and the right side is $0$; the proof begins "let buyer $j$ be the winner". Distinct bids are not needed.
-- source:
--   Golrezaei, Javanmard, Mirrokni, Dynamic Incentive-Aware Learning: Robust Pricing in Contextual Auctions, arXiv:2002.11137v1, p. 57, Lemma 3, (44)–(45)

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_IncentiveAwarePricing_CORP_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace IncentiveAwarePricing.CORP

/-- **Lemma 3**, p. 57, (44)–(45), for one lazy second-price auction with reserves `r`, values
`v` and bids `b`, `N ≥ 2`. The second highest entry of a vector `w` is
`max_{i ≠ j} min{w_i, w_j}`; `s_i = (v_i - b_i)⁺`, `o_i = (b_i - v_i)⁺`, `q = lazyAlloc b r`.
(44): `(v⁻ - b⁻)⁺ ≤ max_i s_i (1 - q_i)`.
(45): if `q_i = 0` and some buyer `j ≠ i` gets the item, then
`(b⁺_{-i} - v⁺_{-i})⁺ ≤ max_{j ≠ i} o_j q_j`. -/
theorem lemma_3 (N : ℕ) (hN : 2 ≤ N) (v b r : Fin N → ℝ) :
    (max ((⨆ p : {p : Fin N × Fin N // p.1 ≠ p.2}, min (v p.1.1) (v p.1.2)) -
        (⨆ p : {p : Fin N × Fin N // p.1 ≠ p.2}, min (b p.1.1) (b p.1.2))) 0 ≤
      ⨆ i : Fin N, max (v i - b i) 0 * (1 - lazyAlloc b r i)) ∧
    ∀ i : Fin N, lazyAlloc b r i = 0 → (∃ j, j ≠ i ∧ lazyAlloc b r j = 1) →
      max ((⨆ j : {j : Fin N // j ≠ i}, b j) - (⨆ j : {j : Fin N // j ≠ i}, v j)) 0 ≤
        ⨆ j : {j : Fin N // j ≠ i}, max (b j - v j) 0 * lazyAlloc b r j := by sorry

end IncentiveAwarePricing.CORP
