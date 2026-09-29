-- Prove2me | Theorems.Thm_Levin2003_tiling_expansion_owf_iff_owf_exists
-- name    : Levin2003.tiling_expansion_owf_iff_owf_exists
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T21:56:47.200984+00:00
-- url     : https://prove2.me/theorems/7a8c4b64-e9e1-4982-909e-1225dffb35c3
-- title:
--   Theorem 1: Tiling Expansion is a owf iff owfs exist
-- statement:
--   **Theorem 1 (Levin 2003, Section 4.3, p. 101).** *Tiling Expansion is a owf if and only if owfs exist.*
--
--   That is: the function $\textsf{TilingExpansion}$ — expand a given top line of tiles to a square using a given set of permitted tiles, and output the bottom line together with the permitted tiles — is a one-way function precisely when some one-way function exists at all. Tiling Expansion is thus a *complete* one-way function, and the first combinatorial one: the existence of one-way functions, the assumption underlying modern cryptography, is equivalent to the hardness of inverting this single explicit tiling problem on uniformly random instances.
--
--   The forward direction is immediate from the definitions once Tiling Expansion is known to be an admissible candidate. The converse carries the content: given any one-way function, its hardness must be transferred to Tiling Expansion, via a universal machine with a step counter whose computation is encoded into a tiled square, with expansion supplying the determinism that an unrestricted tile set lacks.
-- source:
--   L. A. Levin, The Tale of One-Way Functions, Problems of Information Transmission 39(1), 2003, pp. 92-103 (translated from Problemy Peredachi Informatsii, No. 1, 2003, pp. 103-117); preprint https://arxiv.org/abs/cs/0012023, Section 4.3, p. 101, Theorem 1

import Definitions.Def_Levin2003_tiling_expansion

namespace Levin2003

/-- **Theorem 1 (Levin 2003, §4.3).** Tiling Expansion is a one-way function
if and only if one-way functions exist. -/
theorem tiling_expansion_owf_iff_owf_exists :
    OneWay tilingExpansion ↔ ∃ f : Bits → Bits, OneWay f := by
  sorry

end Levin2003
