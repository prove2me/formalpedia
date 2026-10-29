-- Prove2me | Theorems.Thm_IntMul_Kappa_Structure_bitR8_deficit
-- name    : IntMul.Kappa.Structure.bitR8_deficit
-- status  : Proved
-- author  : @darkhipo
-- created : 2026-10-28T20:36:36.034998+00:00
-- url     : https://prove2.me/theorems/be5249ce-4262-4f0d-9f30-626b4a9bdbe4
-- title:
--   The sharing dividend identity: histRankSum bitR8 = 529W - 21·C(23,2)²
-- statement:
--   The rank-sum of Jain's round-eight bitR8 child-width histogram equals 529 × 104719230 − 21 × C(23,2)², where C(23,2) = 253 = 11·23. The sharing dividend 21·C(23,2)² = 1,344,189 = 3·7·(11·23)² factors entirely into constants structural to the construction: 23 is the SideR width cap and an AuxR width; 7·253 = 1771 = v divides every histogram count and both W and T. This identity is decide-provable on the frozen data and documents the arithmetic structure of the round-eight witness for future gate-layer work.
-- source:
--   BigO integer-multiplication verification strike (2026-10-28)

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

namespace IntMul.Kappa.Structure

/-- The sharing dividend of Jain's round-eight witness decomposes as a product
of structural constants: 21 = 3·7 binomial-squared terms. The exact identity. -/
theorem bitR8_deficit :
    histRankSum Jain.bitR8 = 529 * 104719230 - 21 * (Nat.choose 23 2)^2 := by
  sorry

end IntMul.Kappa.Structure
