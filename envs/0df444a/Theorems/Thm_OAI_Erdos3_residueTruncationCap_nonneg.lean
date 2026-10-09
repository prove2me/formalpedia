-- Prove2me | Theorems.Thm_OAI_Erdos3_residueTruncationCap_nonneg
-- name    : OAI.Erdos3.residueTruncationCap_nonneg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:29:21.254913+00:00
-- url     : https://prove2.me/theorems/6e7ebcec-58b1-480a-a09c-618a4f726c08
-- title:
--   The residue truncation cap is nonnegative
-- statement:
--   Let $\iota$ be a finite type with decidable equality, $b$ a natural number and $\eta$ a real number with $0 \le \eta$. Then `residueTruncationCap ι b η` $\ge 0$, where `residueTruncationCap ι b η` $= |\mathcal{D}| \cdot 2^{b} \cdot (1 + \eta)$ and $\mathcal{D} = $ `lowDegreeCoordinateSets ι b` is the family of subsets of $\iota$ with at most $b$ elements.
--
--   Lean: `OAI.Erdos3.residueTruncationCap_nonneg` in `lean/OAI/Combinatorics/Progressions/Geometry/PhysicalBoxControl.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/PhysicalBoxControl.lean#L119

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueTruncationCap_nonneg (ι : Type*) [Fintype ι] [DecidableEq ι]
    (b : ℕ) {eta : ℝ} (heta : 0 ≤ eta) : 0 ≤ residueTruncationCap ι b eta := by
  sorry

end Erdos3
end
end OAI
