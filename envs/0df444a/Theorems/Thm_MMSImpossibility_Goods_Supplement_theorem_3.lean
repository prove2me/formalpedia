-- Prove2me | Theorems.Thm_MMSImpossibility_Goods_Supplement_theorem_3
-- name    : MMSImpossibility.Goods.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:03:31.246203+00:00
-- url     : https://prove2.me/theorems/bbdff1d0-df17-4a77-8e1c-2e7c9b074fc6
-- title:
--   Theorem 3 — for $n\ge 2^{16}$, $\beta_n^{\mathrm{MMS}} \ge 1 + 1/(400000\log_2^2 n)$, witnessed with $n+40\lceil\log_2 n\rceil$ chores
-- statement:
--   Let $n \ge 2^{16}$ be an integer, $k = 8\lceil\log_2 n\rceil$ and $m = n + 5k$. Then:
--
--   1. there are nonnegative additive cost functions $c_1,\dots,c_n$ on $m$ chores such that every agent has $\mathrm{MMS}^{\mathrm{ch}}_i = c_i(M)/n > 0$, and **every** allocation $(B_1,\dots,B_n)$ gives some agent $i$
--
--   $$c_i(B_i) > \Big(1 + \frac{1}{400000\,\log_2^2 n}\Big)\,\mathrm{MMS}^{\mathrm{ch}}_i;$$
--
--   2. consequently the worst-case MMS approximation factor for chores satisfies
--
--   $$\beta_n^{\mathrm{MMS}} \ge 1 + \frac{1}{400000\,\log_2^2 n}.$$
--
--   This is the paper's Theorem 3, $\beta_n^{\mathrm{MMS}} \ge 1 + \Omega((\log n)^{-2})$ for every sufficiently large $n$, witnessed by an additive chores instance with $n + O(\log n)$ chores, in the explicit form its proof establishes. It rules out a $1 + O(n^{-\varepsilon})$ MMS approximation for chores for every fixed $\varepsilon > 0$.
--
--   **Formalization Note** $\log_2^2 n$ is $(\log_2 n)^2$ (`Real.logb 2 n ^ 2`) and $\lceil\log_2 n\rceil$ is `Nat.clog 2 n`, as in the base mission's Theorem 1.
--
--   Differences from the source:
--   - generalization: for every sufficiently large n, β_n^MMS ≥ 1 + Ω((log n)^−2), witnessed by an additive chores instance with n + O(log n) items → for every n ≥ 2^16: an additive chores instance on n + 5·8⌈log₂ n⌉ chores with MMS^ch_i = c_i(M)/n > 0 in which every allocation gives some agent cost > (1 + 1/(400000 log₂² n))·MMS^ch_i, and β_n^MMS ≥ 1 + 1/(400000 log₂² n); reason: the explicit threshold, item count and constant are those of the proof (§4, PDF p. 14: ℓ/µ = 1/(4896k²) > 1/(400000 (log n)²); §2.1, PDF p. 7) and imply the Ω-statement with c = 1/400000 and n + O(log n) chores
--   - encoding: allocations as ordered partitions (B_1,…,B_n) of M; every item allocated → maps A : Fin (n + 5·(8·Nat.clog 2 n)) → Fin n with bundle A i = A⁻¹(i); reason: maps and ordered partitions into possibly empty bundles coincide
--   - encoding: nonnegative additive cost functions c_i : 2^M → ℝ≥0 → real-valued c i : Finset (Fin m) → ℝ with IsAdditive (additivity over singletons and c i S ≥ 0); reason: the same cost functions, nonnegativity stated as a property
--   - encoding: β_n^MMS = sup over instances and β^MMS = sup_{n≥1} β_n^MMS (real suprema, no finiteness asserted) → betaMMS n and betaMMSAll as suprema in EReal of the real ratios; reason: the paper asserts no boundedness; EReal gives the same supremum when it is finite and +∞ otherwise, so the lower bound means exactly what the page says
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, Theorem 3, PDF p. 6 (printed p. 5); explicit constants from its proof, §4, PDF pp. 13–14 (printed pp. 12–13), with n ≥ 2^16, k = 8⌈log n⌉ and m = n + 5k from §2.1, PDF p. 7

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Supplement_Setting

namespace MMSImpossibility.Goods.Supplement

open LittleCharity.MMS MMSImpossibility.Goods

/-- Theorem 3 (PDF p. 6), with the explicit constants of its proof (§4, PDF pp. 13–14, reusing
§2.1 and §2.3): for every integer `n ≥ 2^16`, with `k = 8⌈log₂ n⌉` and `m = n + 5k` chores,
1. there is an additive chores instance on `m` chores in which every agent has
   `MMS^ch_i = c_i(M)/n > 0`, and every allocation gives some agent `i`
   `c_i(B_i) > (1 + 1/(400000 log₂² n)) · MMS^ch_i`;
2. `β_n^MMS ≥ 1 + 1/(400000 log₂² n)`. -/
theorem theorem_3 (n : ℕ) (hn : 2 ^ 16 ≤ n) :
    (∃ c : Fin n → Finset (Fin (n + 5 * (8 * Nat.clog 2 n))) → ℝ,
      IsAdditive c ∧
      (∀ i, mmsCh (c i) n = c i Finset.univ / n) ∧
      (∀ i, 0 < mmsCh (c i) n) ∧
      ∀ A : Fin (n + 5 * (8 * Nat.clog 2 n)) → Fin n, ∃ i,
        (1 + 1 / (400000 * Real.logb 2 n ^ 2)) * mmsCh (c i) n < c i (bundle A i)) ∧
    (((1 + 1 / (400000 * Real.logb 2 n ^ 2) : ℝ)) : EReal) ≤ betaMMS n := by sorry

end MMSImpossibility.Goods.Supplement
