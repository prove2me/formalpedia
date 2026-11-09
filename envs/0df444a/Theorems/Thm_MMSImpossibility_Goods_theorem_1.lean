-- Prove2me | Theorems.Thm_MMSImpossibility_Goods_theorem_1
-- name    : MMSImpossibility.Goods.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:14:10.261472+00:00
-- url     : https://prove2.me/theorems/f9440d9f-7e0d-4f53-b683-d6306227bd4f
-- title:
--   Theorem 1 — for $n\ge 2^{16}$, $\alpha_n^{\mathrm{MMS}} \le 1 - 1/(400000\log_2^2 n)$, witnessed with $n+40\lceil\log_2 n\rceil$ goods
-- statement:
--   Let $n \ge 2^{16}$ be an integer, $k = 8\lceil\log_2 n\rceil$ and $m = n + 5k$. Then:
--
--   1. there are additive nonnegative valuations $v_1,\dots,v_n$ on $m$ goods such that every agent has $\mathrm{MMS}_i = v_i(M)/n > 0$, and **every** allocation $(B_1,\dots,B_n)$ gives some agent $i$
--
--   $$v_i(B_i) < \Big(1 - \frac{1}{400000\,\log_2^2 n}\Big)\,\mathrm{MMS}_i;$$
--
--   2. consequently the worst-case MMS approximation ratio satisfies
--
--   $$\alpha_n^{\mathrm{MMS}} \le 1 - \frac{1}{400000\,\log_2^2 n}.$$
--
--   This is the paper's Theorem 1, $\alpha_n^{\mathrm{MMS}} \le 1-\Omega((\log n)^{-2})$ for every sufficiently large $n$, witnessed by an instance with $n + O(\log n)$ goods and $\mathrm{MMS}_i = \mathrm{PROP}_i$, in the explicit form its proof establishes. It strengthens the $1 - 1/n^4$ bound of Feige, Sapir and Tauber to an inverse-polylogarithmic shortfall.
--
--   **Formalization Note** $\log_2^2 n$ is $(\log_2 n)^2$ (`Real.logb 2 n ^ 2`), $\lceil\log_2 n\rceil$ is `Nat.clog 2 n`; MMS is the published `LittleCharity.MMS.mms`.
--
--   Differences from the source:
--   - generalization: for every sufficiently large n, α_n^MMS ≤ 1 − Ω((log n)^−2), witnessed by an additive goods instance with n + O(log n) items (and MMS_i = PROP_i, PDF p. 5) → for every n ≥ 2^16: an additive instance on n + 5·8⌈log₂ n⌉ items with MMS_i = v_i(M)/n > 0 in which every allocation leaves some agent below (1 − 1/(400000 log₂² n))·MMS_i, and α_n^MMS ≤ 1 − 1/(400000 log₂² n); reason: the explicit threshold and constant are those of the paper's proof (§2.3) and imply the Ω-statement with c = 1/400000 and the n + O(log n) item count
--   - encoding: instances with any finite number of items; allocations as ordered partitions → items Fin m for every m : ℕ; allocations as maps Fin m → Fin n; reason: every finite item set is in bijection with some Fin m; maps and ordered partitions coincide
--   - encoding: nonnegative additive valuations v_i : 2^M → ℝ≥0 → real-valued v i : Finset (Fin m) → ℝ with IsAdditive (additivity over singletons and v i S ≥ 0); reason: the same valuations, nonnegativity stated as a property
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, Theorem 1, PDF p. 5 (printed p. 4); explicit constants from its proof, §2.3, PDF p. 12 (printed p. 11)

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Setting

namespace MMSImpossibility.Goods

open LittleCharity.MMS

/-- Theorem 1 (PDF p. 5), with the explicit constants of its proof (§2.3, PDF p. 12):
for every integer `n ≥ 2^16`, with `k = 8⌈log₂ n⌉` and `m = n + 5k` items,
1. there is an additive goods instance on `m` items in which every agent has
   `MMS_i = v_i(M)/n > 0`, and every allocation gives some agent `i`
   `v_i(B_i) < (1 - 1/(400000 log₂² n)) · MMS_i`;
2. `α_n^MMS ≤ 1 - 1/(400000 log₂² n)`. -/
theorem theorem_1 (n : ℕ) (hn : 2 ^ 16 ≤ n) :
    (∃ v : Fin n → Finset (Fin (n + 5 * (8 * Nat.clog 2 n))) → ℝ,
      IsAdditive v ∧
      (∀ i, mms (v i) n Finset.univ = v i Finset.univ / n) ∧
      (∀ i, 0 < mms (v i) n Finset.univ) ∧
      ∀ A : Fin (n + 5 * (8 * Nat.clog 2 n)) → Fin n, ∃ i,
        v i (bundle A i) <
          (1 - 1 / (400000 * Real.logb 2 n ^ 2)) * mms (v i) n Finset.univ) ∧
    alphaMMS n ≤ 1 - 1 / (400000 * Real.logb 2 n ^ 2) := by sorry

end MMSImpossibility.Goods
