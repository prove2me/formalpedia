-- Prove2me | Theorems.Thm_OAI_Erdos3_SlicedProductBlock_pairDensity_translation_l1_s2
-- name    : OAI.Erdos3.SlicedProductBlock.pairDensity_translation_l1_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:28:53.723284+00:00
-- url     : https://prove2.me/theorems/32848d8f-a9c9-4b8f-8550-cb2b5d6a4c7f
-- title:
--   The pair density of two admissible sliced product blocks is Lipschitz under translation in L1
-- statement:
--   Let $\iota$ be a finite type. A `SlicedProductBlock ι` (a structure defined by OpenAI) consists of real numbers $\mathrm{coefficient}$, $\mathrm{lastLower}$, $\mathrm{lastWidth}$ and functions $\mathrm{lower}, \mathrm{width} : \iota \to \mathbb{R}$; it represents the function $(x, u) \mapsto \mathrm{coefficient} \cdot \prod_{i} (\mathrm{lower}_i + \mathrm{width}_i\, x_i) \cdot (\mathrm{lastLower} + \mathrm{lastWidth}\, u)$ on $(0,1]^\iota \times (0,1]$, which is affine in $u$ with base $\mathrm{coefficient} \cdot \mathrm{lastLower} \cdot \prod_i(\ldots)$ and slope $\mathrm{coefficient} \cdot \mathrm{lastWidth} \cdot \prod_i(\ldots)$. It is `Admissible` (defined by OpenAI) when $\mathrm{coefficient} \ne 0$, $\mathrm{lower}_i \ge 0$ and $\mathrm{width}_i > 0$ for all $i$, and $\mathrm{lastWidth} > 0$.
--
--   Let $A$ and $B$ be admissible sliced product blocks and let $x, y \in \mathbb{R}$. Then
--   $$\int_{\mathbb{R}} \bigl|\texttt{pairDensity}\ A\ B\ (u + x) - \texttt{pairDensity}\ A\ B\ (u + y)\bigr| \, du \;\le\; 2 \cdot \texttt{pairCap}\ A\ B \cdot |x - y|,$$
--   where the integral is the Lebesgue (Bochner) integral over $u \in \mathbb{R}$. Here `pairDensity A B` $: \mathbb{R} \to \mathbb{R}$ is defined by OpenAI as a mixture of normalized interval-window densities: for $(x_1, x_2)$ uniform on $(0,1]^\iota \times (0,1]^\iota$ and $w$ uniform on $(0,1]$, with $a = $ slope of $A$ at $x_1$, $b = $ slope of $B$ at $x_2$ and $c = $ base of $A$ at $x_1$ plus base of $B$ at $x_2$, its value at a point is the average of the normalized indicator (indicator divided by length) of the interval of length $\max(|a|, |b|)$ starting at $c + \min(0, a) + \min(0, b) + \min(|a|, |b|)\, w$. And `pairCap A B` $= 4^{|\iota|} / \min(V_A, V_B)$ (defined by OpenAI), where $V_A = |\mathrm{coefficient}_A| \cdot \mathrm{lastWidth}_A \cdot \prod_i \mathrm{width}_{A,i}$ and likewise for $B$.
--
--   Lean: `OAI.Erdos3.SlicedProductBlock.pairDensity_translation_l1_s2`, which states OpenAI's `OAI.Erdos3.SlicedProductBlock.pairDensity_translation_l1` (in `lean/OAI/Combinatorics/Progressions/Probability/SlicedPairDensity.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B048`, `OAIE3v2B061` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/SlicedPairDensity.lean (declaration OAI.Erdos3.SlicedProductBlock.pairDensity_translation_l1)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B048
import Definitions.Def_OAIE3v2B061

section

namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory

variable {ι : Type*} [Fintype ι]

theorem pairDensity_translation_l1_s2 {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (x y : ℝ) :
    (∫ u, |pairDensity A B (u + x) - pairDensity A B (u + y)|) ≤
      2 * pairCap A B * |x - y| := by
  sorry

end Erdos3.SlicedProductBlock

end

end OAI
end
