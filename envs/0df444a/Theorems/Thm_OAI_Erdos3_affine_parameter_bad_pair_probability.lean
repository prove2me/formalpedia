-- Prove2me | Theorems.Thm_OAI_Erdos3_affine_parameter_bad_pair_probability
-- name    : OAI.Erdos3.affine_parameter_bad_pair_probability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:42:02.197178+00:00
-- url     : https://prove2.me/theorems/6ed8e7bc-7d4b-42ea-baa4-c88ce95d9cec
-- title:
--   Probability that two uniform box points form an affine-parameter bad pair
-- statement:
--   Let $J$ be a finite type with decidable equality and $|J|\ge2$, and let $\mathrm{lo},\mathrm{hi}\colon J\to\mathbb Z$ with $\mathrm{lo}_j<\mathrm{hi}_j$ for all $j$. Let $D,Q,B,R,r\in\mathbb N$ and $a\colon J\to\mathbb Z$ with $DB\le Q$ and $0<B$, and let $L>0$ be real with $L\le\mathrm{hi}_j-\mathrm{lo}_j\le R$ for every $j$. Draw $x,y$ independently and uniformly from the integer box $\prod_j\{\mathrm{lo}_j,\dots,\mathrm{hi}_j-1\}$ (each from `integerBoxUniformWeights lo hi hlen`, the product of the uniform weights on the intervals, combined with the product weights `prod`). Then the probability of `affineParameterBadPair D Q r a x y` is at most `integerBoxBadPairBudget |J| B R r L`. Here `affineParameterBadPair D Q r a x y` holds when either $Q<\big|\gcd_j\big((a_j+Dy_j)-(a_j+Dx_j)\big)\big|$ (the content of the difference vector, `BohrLattice.Primitive.content`) or $|y_j-x_j|\le r$ for every $j$; and
--   $$\texttt{integerBoxBadPairBudget}\ d\ B\ R\ r\ L=2^{d-1}\Big(\frac1{B^{d-1}}+\frac R{L^d}\Big)+\Big(\frac{2r+1}L\Big)^d,$$
--   with $d-1$ the natural-number subtraction.
--
--   Lean: `OAI.Erdos3.affine_parameter_bad_pair_probability` in `lean/OAI/Combinatorics/Progressions/Lattices/AffineMeshRetention.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B016` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineMeshRetention.lean#L196

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B016

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_parameter_bad_pair_probability {J : Type*}
    [Fintype J] [DecidableEq J] (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (D Q B R r : ℕ) (a : J → ℤ) (hBQ : D * B ≤ Q) (hB : 0 < B)
    (hdim : 2 ≤ Fintype.card J) {L : ℝ} (hL : 0 < L)
    (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ))
    (hwidth : ∀ j, hi j - lo j ≤ (R : ℤ)) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
      (fun xy => affineParameterBadPair D Q r a
        (fun j => (xy.1 j : ℤ)) (fun j => (xy.2 j : ℤ))) ≤
      integerBoxBadPairBudget (Fintype.card J) B R r L := by
  sorry

end Erdos3
end
end OAI
