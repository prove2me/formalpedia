-- Prove2me | Theorems.Thm_OAI_Erdos3_RelativePatchSliceConclusion_mono
-- name    : OAI.Erdos3.RelativePatchSliceConclusion.mono
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T23:08:59.882048+00:00
-- url     : https://prove2.me/theorems/d9697f65-ff50-4e10-bb50-560fcf85b0e8
-- title:
--   The relative patch slice conclusion is monotone in the rank bound and the cost
-- statement:
--   Let $X$ be a finite type, $s \in \mathbb{N}$, $N : X \to \mathbb{N}$, $f : \mathbb{Z}^X \to \mathbb{R}$, $\mathrm{target} \in \mathbb{R}$, $\mathrm{rankBound}, \mathrm{rankBound}' \in \mathbb{N}$ and $\mathrm{cost}, \mathrm{cost}' \in \mathbb{R}$. Here `RelativePatchSliceConclusion s N f target rankBound cost` is a predicate of OpenAI asserting that there exist $q > 0$, a residue box slice $S$ (`ResidueBoxSlice N q`), a natural number $d$ and a `PolynomialPatch X s d` $A$ such that $e^{-\mathrm{cost}} N_i \le \mathrm{length}_i(S)$ for every $i$, $d \le \mathrm{rankBound}$, `relativePatchComplexity A` $\le \mathrm{cost}$, and $e^{-\mathrm{cost}} \le$ `relativePatchSliceScore S f target A`. Assume `RelativePatchSliceConclusion s N f target rankBound cost`, $\mathrm{rankBound} \le \mathrm{rankBound}'$ and $\mathrm{cost} \le \mathrm{cost}'$. Then `RelativePatchSliceConclusion s N f target rankBound' cost'`.
--
--   Lean: `OAI.Erdos3.RelativePatchSliceConclusion.mono` in `lean/OAI/Combinatorics/Progressions/Estimates/RelativePatchAmplification.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B100` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/RelativePatchAmplification.lean#L91

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B100

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem RelativePatchSliceConclusion.mono {X : Type*} [Fintype X] {s : ℕ}
    {N : X → ℕ} {f : (X → ℤ) → ℝ} {target : ℝ} {rankBound rankBound' : ℕ}
    {cost cost' : ℝ} (h : RelativePatchSliceConclusion s N f target rankBound cost)
    (hrank : rankBound ≤ rankBound') (hcost : cost ≤ cost') :
    RelativePatchSliceConclusion s N f target rankBound' cost' := by
  sorry

end Erdos3
end
end OAI
