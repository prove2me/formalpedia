-- Prove2me | Theorems.Thm_OAI_finiteCircle_fullMain
-- name    : OAI.finiteCircle_fullMain
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:41.066686+00:00
-- url     : https://prove2.me/theorems/88a71807-ae20-4e7c-b7ba-02e74140c11f
-- statement:
--   The theorem states that FullMain holds, an existential statement about edit-distance embeddings into real ℓ¹. Here editDistance(x,y) is the least number of single-letter insertions, deletions or substitutions turning list x into y; lcs is the maximal length of a common subsequence and deficit(x,y)=|x|−lcs(x,y). The distortion of an embedding f of a family of words into ℓ¹(ℕ) is (sup of ‖f x−f y‖/ed over distinct pairs) times (sup of ed/‖f x−f y‖), and E(α,d) is the infimum of this distortion over injective embeddings of the words of length at most d over alphabet α. The claim is that there are positive reals c, C, a, Ccode, δ, ε and a natural number d₀ such that four things hold. First, TwoCodes(a,Ccode,δ,ε): for every finite alphabet α with at least 2 letters there exist a block length w and a binary code c: α→{0,1}^w, and separately another such code, each satisfying SubstitutionBounds (0<w, w ≤ Ccode·log(2|α|), the encoded deficit of equal-length words lies between a·w times and w times the original deficit, and encoded edit distance is at most w times the original), the first also being OffsetLocal δ (distinct letters have length-w/8 intervals, at any offsets, with lcs at most (1−δ)·w/8) and the second AnchorLocal ε (a long, nearly contiguous matching of at least w/4 increasing positions between codewords of a and b forces a=b and some matched pair of equal positions). Second, UniformUpper(C,d₀): for every finite alphabet with at least 2 letters and every d≥d₀ there is a map of the words of length at most d into some ℝ^M, with ℓ¹ distances at least the edit distance and at most exp(C·√(log d·log log d)) times it. Third, for all such alphabets and d≥d₀, exp(c·√(log d·log log d)) ≤ E(α,d) ≤ exp(C·√(log d·log log d)). Fourth, for every d≥d₀: MaskWitness and ExcludedWitness hold with constant c, meaning explicit binary-encoded families built from prime-indexed circular-shift constructions, of common length n with 0<n≤d, using the offset-local and anchor-local codes respectively, whose optimal distortion is at least exp(c·√(log d·log log d)); and the supremum of E(Fin A,d) over all A≥2 also lies between exp(c·√(log d·log log d)) and exp(C·√(log d·log log d)).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FiniteCircle.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FiniteCircle.lean; bytes 10094..10161
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_FiniteCircle

namespace OAI

theorem finiteCircle_fullMain : FiniteCircle.FullMain := by
  sorry

end OAI
