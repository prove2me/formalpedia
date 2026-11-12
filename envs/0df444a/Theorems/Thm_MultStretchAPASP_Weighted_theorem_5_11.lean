-- Prove2me | Theorems.Thm_MultStretchAPASP_Weighted_theorem_5_11
-- name    : MultStretchAPASP.Weighted.theorem_5_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:10:03.103503+00:00
-- url     : https://prove2.me/theorems/569db50d-06d6-4f94-81e4-e00ffd65eb2c
-- title:
--   Theorem 5.11 — cyclic invariance ω(a, a, b) = ω(a, b, a) = ω(b, a, a)
-- statement:
--   For all $a,b>0$, the rectangular matrix multiplication exponent of §2.4 satisfies
--   $$\omega(a,a,b)=\omega(a,b,a)=\omega(b,a,a).$$
--
--   The paper cites it from [7] and uses it, with Observation 5.10, to simplify the running time in the proof of Lemma 5.16.
--
--   **Formalization Note.** $\omega(\cdot,\cdot,\cdot)$ is the paper's operational exponent (running time on the word RAM), the one every other item of the mission uses.
--
--   Differences from the source:
--
--   - reading: ω(a, b, c): "the infimum over all τ > 0 such that, for every constant ε > 0, the product A·B can be computed in O(n^{τ+ε}) runtime" (p. 7), A ∈ ℝ^{n^a×n^b}, B ∈ ℝ^{n^b×n^c}; ω = ω(1, 1, 1) → omega3 a b c: the infimum of the τ > 0 achievable, for every ε > 0, by a deterministic program of the word RAM of DynConnWC_Program in C·N^{τ+ε} + C steps on natural-number matrices of sizes ⌈N^a⌉ × ⌈N^b⌉ and ⌈N^b⌉ × ⌈N^c⌉; omega = omega3 1 1 1; reason: the paper defines ω by running time and names no machine; a word RAM takes integer inputs; deterministic because Theorem 2.14 claims a deterministic algorithm in time n^{ω(1,r,1)+o(1)}; the same machine runs every algorithm of the mission
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 28, Theorem 5.11

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MultStretchAPASP_Weighted_OmegaExp

set_option autoImplicit false

namespace MultStretchAPASP.Weighted

/-- **Theorem 5.11** (p. 28, cited from [7]). For all `a, b > 0`,
`ω(a, a, b) = ω(a, b, a) = ω(b, a, a)`, for the operational exponent `ω(·, ·, ·)` of §2.4. -/
theorem theorem_5_11 :
    ∀ a b : ℝ, 0 < a → 0 < b →
      omega3 a a b = omega3 a b a ∧ omega3 a b a = omega3 b a a := by sorry

end MultStretchAPASP.Weighted
