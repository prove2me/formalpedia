-- Prove2me | Theorems.Thm_MMSImpossibility_Goods_lemma_5
-- name    : MMSImpossibility.Goods.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:14:01.471285+00:00
-- url     : https://prove2.me/theorems/cf7601d3-0ff6-430b-9c4a-56f80c380e08
-- title:
--   Lemma 5 — a balanced code of size $\ge 2^{k/8}$ with minimum distance $\ge k/4$
-- statement:
--   For every integer $k \ge 128$ divisible by $8$ there is a code $C \subseteq L_k$ of balanced words of length $k$ with
--
--   $$|C| \ge 2^{k/8} \quad\text{and}\quad d_H(a,b) \ge \frac k4 \ \text{ for all distinct } a,b\in C,$$
--
--   where $d_H$ is the Hamming distance. This constant-weight code supplies the $n$ distinct agent types of the construction (it has $2^{k/8} \ge n$ codewords for $k = 8\lceil\log_2 n\rceil$).
--
--   Differences from the source:
--   - encoding: minimum Hamming distance at least k/4; words in {0,1}^k → k ≤ 4·d_H(a, b) for all distinct a, b ∈ C; words Fin k → Fin 2; reason: multiplying out k/4 gives the same condition; the word encoding changes no instance
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, Lemma 5, PDF p. 7 (printed p. 6); proof in Appendix A, PDF p. 17 (printed p. 16)

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Code

namespace MMSImpossibility.Goods

/-- Lemma 5 (PDF p. 7): for every integer `k ≥ 128` divisible by `8` there is a code
`C ⊆ L_k` with `|C| ≥ 2^{k/8}` and minimum Hamming distance at least `k/4`, i.e. any two
distinct codewords differ in at least `k/4` coordinates (written `k ≤ 4 · d_H(a, b)`). -/
theorem lemma_5 (k : ℕ) (hk : 128 ≤ k) (h8 : 8 ∣ k) :
    ∃ C : Finset (Fin k → Fin 2), C ⊆ balancedWords k ∧ 2 ^ (k / 8) ≤ C.card ∧
      ∀ a ∈ C, ∀ b ∈ C, a ≠ b → k ≤ 4 * hammingDist a b := by sorry

end MMSImpossibility.Goods
