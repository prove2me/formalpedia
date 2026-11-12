-- Prove2me | Theorems.Thm_MultStretchAPASP_Weighted_partition_bound
-- name    : MultStretchAPASP.Weighted.partition_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:09:58.634855+00:00
-- url     : https://prove2.me/theorems/7ac6e39c-378d-453e-9b92-3ea08bec7a04
-- title:
--   §5.2 (proof of Lemma 5.16) — ω(1 − a, 1, 1 − a) ≤ a + (1 − a)ω by splitting the inner dimension
-- statement:
--   For $a\in[0,1]$, partitioning the inner dimension of an $n^{1-a}\times n$ by $n\times n^{1-a}$ product into $O(n^a)$ blocks reduces it to $O(n^a)$ square products of dimension $O(n^{1-a})$; hence, with $\omega=\omega(1,1,1)$,
--   $$\omega(1-a,1,1-a)\ \le\ a+(1-a)\,\omega.$$
--
--   This is the step that turns the general bound of Lemma 5.16 into the exponent $\omega-\frac{(\omega-2)^2}{\omega-1}$ at $a=\frac{\omega-2}{\omega-1}$.
--
--   Differences from the source:
--
--   - reading: the displayed inequality (no range of a printed beside it) → for every a ∈ [0, 1]; reason: it is applied to the parameter a ∈ [0, 1] of Lemma 5.16
--   - reading: ω(a, b, c): "the infimum over all τ > 0 such that, for every constant ε > 0, the product A·B can be computed in O(n^{τ+ε}) runtime" (p. 7), A ∈ ℝ^{n^a×n^b}, B ∈ ℝ^{n^b×n^c}; ω = ω(1, 1, 1) → omega3 a b c: the infimum of the τ > 0 achievable, for every ε > 0, by a deterministic program of the word RAM of DynConnWC_Program in C·N^{τ+ε} + C steps on natural-number matrices of sizes ⌈N^a⌉ × ⌈N^b⌉ and ⌈N^b⌉ × ⌈N^c⌉; omega = omega3 1 1 1; reason: the paper defines ω by running time and names no machine; a word RAM takes integer inputs; deterministic because Theorem 2.14 claims a deterministic algorithm in time n^{ω(1,r,1)+o(1)}; the same machine runs every algorithm of the mission
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 32, §5.2, proof of Lemma 5.16 (displayed inequality)

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MultStretchAPASP_Weighted_OmegaExp

set_option autoImplicit false

namespace MultStretchAPASP.Weighted

/-- **§5.2, proof of Lemma 5.16** (p. 32, displayed): splitting the inner dimension into `O(n^a)`
blocks gives `ω(1 − a, 1, 1 − a) ≤ a + (1 − a)·ω` for every `a ∈ [0, 1]`. -/
theorem partition_bound :
    ∀ a : ℝ, 0 ≤ a → a ≤ 1 → omega3 (1 - a) 1 (1 - a) ≤ a + (1 - a) * omega := by sorry

end MultStretchAPASP.Weighted
