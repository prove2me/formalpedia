-- Prove2me | Theorems.Thm_MultStretchAPASP_Weighted_observation_5_10
-- name    : MultStretchAPASP.Weighted.observation_5_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:10:08.053268+00:00
-- url     : https://prove2.me/theorems/78122307-e959-4658-a8fe-de061c27b0d2
-- title:
--   Observation 5.10 — ω(1 − a, 1, 1 − a) + a ≥ ω(1, 1, 1 − a)
-- statement:
--   For $a\in[0,1]$, with the operational rectangular exponent $\omega(\cdot,\cdot,\cdot)$ of §2.4,
--   $$\omega(1-a,1,1-a)+a\ \ge\ \omega(1,1,1-a).$$
--
--   It lets the proof of Lemma 5.16 bound the cost of lines 10–11 of Algorithm 10 by the cost of the bucket loop.
--
--   Differences from the source:
--
--   - reading: ω(a, b, c): "the infimum over all τ > 0 such that, for every constant ε > 0, the product A·B can be computed in O(n^{τ+ε}) runtime" (p. 7), A ∈ ℝ^{n^a×n^b}, B ∈ ℝ^{n^b×n^c}; ω = ω(1, 1, 1) → omega3 a b c: the infimum of the τ > 0 achievable, for every ε > 0, by a deterministic program of the word RAM of DynConnWC_Program in C·N^{τ+ε} + C steps on natural-number matrices of sizes ⌈N^a⌉ × ⌈N^b⌉ and ⌈N^b⌉ × ⌈N^c⌉; omega = omega3 1 1 1; reason: the paper defines ω by running time and names no machine; a word RAM takes integer inputs; deterministic because Theorem 2.14 claims a deterministic algorithm in time n^{ω(1,r,1)+o(1)}; the same machine runs every algorithm of the mission
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 28, Observation 5.10

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MultStretchAPASP_Weighted_OmegaExp

set_option autoImplicit false

namespace MultStretchAPASP.Weighted

/-- **Observation 5.10** (p. 28). For every `a ∈ [0, 1]`, `ω(1 − a, 1, 1 − a) + a ≥ ω(1, 1, 1 − a)`. -/
theorem observation_5_10 :
    ∀ a : ℝ, 0 ≤ a → a ≤ 1 → omega3 1 1 (1 - a) ≤ omega3 (1 - a) 1 (1 - a) + a := by sorry

end MultStretchAPASP.Weighted
