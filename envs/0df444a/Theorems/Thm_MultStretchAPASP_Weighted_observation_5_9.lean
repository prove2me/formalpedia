-- Prove2me | Theorems.Thm_MultStretchAPASP_Weighted_observation_5_9
-- name    : MultStretchAPASP.Weighted.observation_5_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:10:13.039316+00:00
-- url     : https://prove2.me/theorems/77918b15-4d37-480c-8747-d608e6abd8b1
-- title:
--   Observation 5.9 — ω(1 − a, 1, 1 − a) + a − 1 ≥ 1
-- statement:
--   For $a\in[0,1]$ let $\omega(1-a,1,1-a)$ be the exponent of multiplying an $n^{1-a}\times n$ matrix by an $n\times n^{1-a}$ matrix (the operational exponent of §2.4). Then
--   $$\omega(1-a,1,1-a)+a-1\ \ge\ 1\qquad\text{for every }a\in[0,1].$$
--
--   It is used in Lemma 5.12 to absorb the $O(|Y_{i,j}|n)$ bookkeeping of an iteration into the bound $|Y_{i,j}|\,n^{\omega(1-a,1,1-a)+a-1}$.
--
--   Differences from the source:
--
--   - reading: ω(a, b, c): "the infimum over all τ > 0 such that, for every constant ε > 0, the product A·B can be computed in O(n^{τ+ε}) runtime" (p. 7), A ∈ ℝ^{n^a×n^b}, B ∈ ℝ^{n^b×n^c}; ω = ω(1, 1, 1) → omega3 a b c: the infimum of the τ > 0 achievable, for every ε > 0, by a deterministic program of the word RAM of DynConnWC_Program in C·N^{τ+ε} + C steps on natural-number matrices of sizes ⌈N^a⌉ × ⌈N^b⌉ and ⌈N^b⌉ × ⌈N^c⌉; omega = omega3 1 1 1; reason: the paper defines ω by running time and names no machine; a word RAM takes integer inputs; deterministic because Theorem 2.14 claims a deterministic algorithm in time n^{ω(1,r,1)+o(1)}; the same machine runs every algorithm of the mission
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 28, Observation 5.9

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MultStretchAPASP_Weighted_OmegaExp

set_option autoImplicit false

namespace MultStretchAPASP.Weighted

/-- **Observation 5.9** (p. 28). For every `a ∈ [0, 1]`, `ω(1 − a, 1, 1 − a) + a − 1 ≥ 1`. -/
theorem observation_5_9 :
    ∀ a : ℝ, 0 ≤ a → a ≤ 1 → 1 ≤ omega3 (1 - a) 1 (1 - a) + a - 1 := by sorry

end MultStretchAPASP.Weighted
