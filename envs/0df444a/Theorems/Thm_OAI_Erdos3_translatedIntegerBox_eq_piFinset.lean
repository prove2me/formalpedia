-- Prove2me | Theorems.Thm_OAI_Erdos3_translatedIntegerBox_eq_piFinset
-- name    : OAI.Erdos3.translatedIntegerBox_eq_piFinset
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:20:52.773042+00:00
-- url     : https://prove2.me/theorems/d01fd044-c2e0-4d4f-944d-5ae72ca2e356
-- title:
--   A translated integer box is the product of the intervals [lo_i, lo_i + N_i)
-- statement:
--   Let $I$ be a finite type with decidable equality, $\mathrm{lo} : I\to\mathbb{Z}$ and $N : I\to\mathbb{N}$. Then `translatedIntegerBox lo N` (the translate by $\mathrm{lo}$ of `integerBox N`, the finite set $\prod_{i\in I}\{0,1,\dots,N_i-1\}\subseteq\mathbb{Z}^I$) equals, as a finite subset of $\mathbb{Z}^I$, the product set
--   $$\prod_{i\in I}\,[\mathrm{lo}_i,\ \mathrm{lo}_i+N_i)\cap\mathbb{Z}$$
--   (Mathlib's `Fintype.piFinset` of the integer intervals `Finset.Ico (lo i) (lo i + N i)`).
--
--   Lean: `OAI.Erdos3.translatedIntegerBox_eq_piFinset` in `lean/OAI/Combinatorics/Progressions/Geometry/PhysicalBoxPartition.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B008` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/PhysicalBoxPartition.lean#L73

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B008

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem translatedIntegerBox_eq_piFinset (lo : I → ℤ) (N : I → ℕ) :
    translatedIntegerBox lo N = Fintype.piFinset (fun i => Finset.Ico (lo i) (lo i + N i)) := by
  sorry

end Erdos3
end
end OAI
