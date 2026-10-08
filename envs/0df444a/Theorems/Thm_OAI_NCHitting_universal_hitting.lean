-- Prove2me | Theorems.Thm_OAI_NCHitting_universal_hitting
-- name    : OAI.NCHitting.universal_hitting
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:57.581367+00:00
-- url     : https://prove2.me/theorems/84222277-607d-454b-afea-5765d5771654
-- statement:
--   The theorem states that, for natural numbers n,s ≥ 1 and any field F of characteristic zero, every noncommutative arithmetic formula f over F in n variables x₀,…,xₙ₋₁ (built from scalars of F, single variables, binary addition and binary multiplication, with size counting each scalar or variable leaf as 1 and each addition or multiplication node as the sizes of its two parts plus 1) satisfies the following. If f.size ≤ s and f is not the zero series, meaning its noncommutative coefficient series has some nonzero coefficient on a word w in the variables, then evaluating f at an explicit tuple of rational matrices gives a nonzero matrix. Here scalars a of F are sent to the scalar matrix a times the identity of size D, where D = dimension(n,s) equals 1 if n = s = 1 and 2ns² otherwise, and the variable xᵢ is sent to the D×D matrix generator(i), viewed over F via the rational cast. For n = s = 1 this matrix is the 1×1 matrix with entry 1. Otherwise its entry in row r and column q (indexed from zero) is (−1)^(r−q−1) / (r·(i+1)^(r−q)) when q < r, and 0 when q ≥ r. The coefficient series of a formula is defined by letting scalars give a constant series, a variable give the indicator of its one-letter word, addition add series termwise, and multiplication give the noncommutative convolution (Cauchy product over word concatenation).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FormulaHitting.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FormulaHitting.lean; bytes 1741..2043
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Definitions.Def_FormulaHitting

namespace OAI

namespace NCHitting

universe u_2

theorem universal_hitting (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s)
    (F : Type u_2) [Field F] [CharZero F] (f : Formula F n)
    (hsize : f.size ≤ s) (hf : ∃ w, f.coeff w ≠ 0) :
    f.eval (Matrix.scalar (Fin (dimension n s)))
      (fun i r q => (generator n s i r q : F)) ≠ 0 := by
  sorry

end NCHitting
end OAI
