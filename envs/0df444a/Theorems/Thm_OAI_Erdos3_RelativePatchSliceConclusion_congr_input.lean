-- Prove2me | Theorems.Thm_OAI_Erdos3_RelativePatchSliceConclusion_congr_input
-- name    : OAI.Erdos3.RelativePatchSliceConclusion.congr_input
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T23:32:37.617868+00:00
-- url     : https://prove2.me/theorems/d9702b08-b4e3-41e5-93a1-bf6689afba1e
-- title:
--   The relative patch slice conclusion depends only on the input inside the box
-- statement:
--   Let $X$ be a finite type, $s, \mathrm{rankBound} \in \mathbb{N}$, $N : X \to \mathbb{N}$, $f, g : \mathbb{Z}^X \to \mathbb{R}$, and $\mathrm{target}, \mathrm{cost} \in \mathbb{R}$. Here `RelativePatchSliceConclusion s N f target rankBound cost` is a predicate of OpenAI asserting that there exist $q > 0$, a residue box slice $S$ (`ResidueBoxSlice N q`: start points and lengths per coordinate, with every point $\mathrm{start}_i + q j$, $j < \mathrm{length}_i$, below $N_i$), a natural number $d$ and a `PolynomialPatch X s d` $A$ such that $e^{-\mathrm{cost}} N_i \le \mathrm{length}_i$ for every $i$, $d \le \mathrm{rankBound}$, `relativePatchComplexity A` $\le \mathrm{cost}$, and $e^{-\mathrm{cost}} \le$ `relativePatchSliceScore S f target A`. Assume `RelativePatchSliceConclusion s N f target rankBound cost`, and that $f(x) = g(x)$ for every $x$ in `integerBox N` (the box $\prod_i \{0, \dots, N_i - 1\} \subseteq \mathbb{Z}^X$). Then `RelativePatchSliceConclusion s N g target rankBound cost`.
--
--   Lean: `OAI.Erdos3.RelativePatchSliceConclusion.congr_input` in `lean/OAI/Combinatorics/Progressions/Geometry/RelativePatchBoxRestriction.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B100` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/RelativePatchBoxRestriction.lean#L71

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B100

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem RelativePatchSliceConclusion.congr_input {X : Type*} [Fintype X]
    {s : ℕ} {N : X → ℕ} {f g : (X → ℤ) → ℝ}
    {target cost : ℝ} {rankBound : ℕ}
    (h : RelativePatchSliceConclusion s N f target rankBound cost)
    (hfg : ∀ x ∈ integerBox N, f x = g x) :
    RelativePatchSliceConclusion s N g target rankBound cost := by
  sorry

end Erdos3
end
end OAI
