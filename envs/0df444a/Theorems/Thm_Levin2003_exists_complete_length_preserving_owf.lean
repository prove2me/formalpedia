-- Prove2me | Theorems.Thm_Levin2003_exists_complete_length_preserving_owf
-- name    : Levin2003.exists_complete_length_preserving_owf
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T22:01:03.98326+00:00
-- url     : https://prove2.me/theorems/5156a12d-c347-44be-8533-3273a3023c65
-- title:
--   A complete length-preserving one-way function exists
-- statement:
--   There is a polynomial-time computable, length-preserving function $U$ that is one-way if and only if one-way functions exist at all.
--
--   This is the computational counterpart of the goal theorem, and the first step of the reduction sketched in Section 4.3: *'A complete owf is easy to construct as a modification of a universal Turing Machine (UTM). ... We start with a UTM, add a time counter that aborts after, say, $n^2$ steps. We preserve a copy of the program prefix and force it, as well as the input length, on the output. This produces a complete \"computational\" length-preserving owf.'* Length preservation of such a $U$ rests on Section 4.2, where any one-way function is turned into a length-preserving one by separating siblings with a universal hash family and hashing instances down to the length of the witnesses (Proposition 2).
--
--   Note that the statement asked for here is the bare existence of a complete length-preserving one-way function candidate; the quantitative security relation of the paper's Proposition 2 is not expressible in this mission's model and is not claimed.
-- source:
--   L. A. Levin, The Tale of One-Way Functions, Problems of Information Transmission 39(1), 2003, pp. 92-103 (translated from Problemy Peredachi Informatsii, No. 1, 2003, pp. 103-117); preprint https://arxiv.org/abs/cs/0012023, Section 4.2 (p. 100, Proposition 2) and Section 4.3 (p. 102, 'The reduction')

import Definitions.Def_Levin2003_tiling_expansion

namespace Levin2003

/-- There is a complete length-preserving one-way function candidate: a
polynomial-time computable, length-preserving function that is one-way exactly
when one-way functions exist at all. -/
theorem exists_complete_length_preserving_owf :
    ∃ U : Bits → Bits, PolyTimeComputable U ∧ LengthPreserving U ∧
      (OneWay U ↔ ∃ f : Bits → Bits, OneWay f) := by
  sorry

end Levin2003
