-- Prove2me | Theorems.Thm_Levin2003_tilingExpansion_owf_of_exists_owf
-- name    : Levin2003.tilingExpansion_owf_of_exists_owf
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T22:02:27.904761+00:00
-- url     : https://prove2.me/theorems/d0d3b002-40f1-4013-8eed-34afe00a2310
-- title:
--   Theorem 1, hard direction: owfs exist implies Tiling Expansion is one-way
-- statement:
--   If some one-way function exists, then Tiling Expansion is itself one-way.
--
--   This is the substantial half of Theorem 1: hardness, wherever it lives, transfers to the tiling problem. Its proof combines the completeness of a universal length-preserving function with the reduction of a machine computation to a tiled square, and additionally requires that the encoding used not distort the uniform distribution on instances of a given length by more than a polynomial factor — an inverter for Tiling Expansion succeeding on a noticeable fraction of uniformly random tiling instances must yield an inverter for the given one-way function succeeding on a noticeable fraction of uniformly random inputs. The converse implication is immediate, as Tiling Expansion witnesses the existential; the two together give the goal theorem.
-- source:
--   L. A. Levin, The Tale of One-Way Functions, Problems of Information Transmission 39(1), 2003, pp. 92-103 (translated from Problemy Peredachi Informatsii, No. 1, 2003, pp. 103-117); preprint https://arxiv.org/abs/cs/0012023, Section 4.3, p. 101, Theorem 1 (nontrivial direction)

import Definitions.Def_Levin2003_tiling_expansion

namespace Levin2003

/-- The hard half of Theorem 1: if some one-way function exists, then Tiling
Expansion is itself one-way. -/
theorem tilingExpansion_owf_of_exists_owf :
    (∃ f : Bits → Bits, OneWay f) → OneWay tilingExpansion := by
  sorry

end Levin2003
