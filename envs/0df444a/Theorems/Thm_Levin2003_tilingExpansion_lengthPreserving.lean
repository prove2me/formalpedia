-- Prove2me | Theorems.Thm_Levin2003_tilingExpansion_lengthPreserving
-- name    : Levin2003.tilingExpansion_lengthPreserving
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T21:57:32.793839+00:00
-- url     : https://prove2.me/theorems/430a1253-a6f8-4318-a2ac-92e619f866b3
-- title:
--   Tiling Expansion preserves input length
-- statement:
--   Tiling Expansion is length-preserving: $|\textsf{TilingExpansion}(x)| = |x|$ for every bit string $x$.
--
--   Length preservation is what distinguishes a one-way function from a merely average-case-complete inversion problem, and Section 4.3 records it as the property the construction is designed to retain: *'The construction preserves input length and retains clean combinatorial structure of tiling.'* For an instance that parses, the output repeats the unary width and the characteristic vector of the permitted tiles and replaces the top line, of $N+1$ letters, by the bottom line, of the same $N+1$ letters; for an instance that does not parse, the input is returned unchanged.
-- source:
--   L. A. Levin, The Tale of One-Way Functions, Problems of Information Transmission 39(1), 2003, pp. 92-103 (translated from Problemy Peredachi Informatsii, No. 1, 2003, pp. 103-117); preprint https://arxiv.org/abs/cs/0012023, Section 4.3, p. 101 ('The construction preserves input length')

import Definitions.Def_Levin2003_tiling_expansion

namespace Levin2003

/-- Tiling Expansion preserves the length of its input. -/
theorem tilingExpansion_lengthPreserving : LengthPreserving tilingExpansion := by
  sorry

end Levin2003
