-- Prove2me | Theorems.Thm_OAI_RationalHitting_main
-- name    : OAI.RationalHitting.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:14.964988+00:00
-- url     : https://prove2.me/theorems/57f21b19-c392-4b9c-9966-923816483101
-- statement:
--   The theorem states that the defined proposition MainStatement holds, with no further hypotheses. Formulas in n variables are built from the variables, rational constants, sums, products and unary inverses, with size counting nodes. A formula evaluates at a tuple X of n rational d×d matrices to a matrix v when variables are read from X, constants a become the scalar matrix a, and an inverse node returns b only if the evaluated operand a satisfies ab = ba = 1, so inversion is partial. A formula is admissible if for some d>0 and some tuple it evaluates to some matrix, and nonzero if some such evaluation gives a nonzero matrix. An output of dimension d>0 is a list of n-tuples of rational d×d matrices; it is encoded as a bit string by self-delimiting binary encodings of d, of the list length, and of every matrix entry (sign bit, numerator magnitude and reduced denominator). An output H hits size bound s if, for every admissible nonzero formula of size at most s, some tuple in H makes the formula evaluate to an invertible matrix. MainStatement asserts that there are a deterministic TM0 Turing machine G with a finite state set and 4-symbol alphabet (no oracle or advice) and positive naturals C and k such that, for all n≥1 and s≥1, some output H of n-tuples exists with dimension at most C(n+s+1)^k, encoded length at most C(n+s+1)^k, and hits size bound s, and G, started on the unary input of n twos, a one, then s twos, halts after at most C(n+s+1)^k steps with the encoding of H, as binary digits 1 and 2, as the tape content to the right of its head.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RationalHitting.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RationalHitting.lean; bytes 4196..4238
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_RationalHitting

namespace OAI

namespace RationalHitting

universe u

theorem main : MainStatement := by
  sorry

end RationalHitting
end OAI
