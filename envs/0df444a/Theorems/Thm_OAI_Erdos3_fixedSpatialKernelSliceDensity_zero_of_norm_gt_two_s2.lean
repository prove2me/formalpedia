-- Prove2me | Theorems.Thm_OAI_Erdos3_fixedSpatialKernelSliceDensity_zero_of_norm_gt_two_s2
-- name    : OAI.Erdos3.fixedSpatialKernelSliceDensity_zero_of_norm_gt_two_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:40:55.315374+00:00
-- url     : https://prove2.me/theorems/5fd9d534-fec9-42fe-95bd-36b9af0fac7b
-- title:
--   The fixed spatial kernel slice density vanishes at points of sup norm greater than two
-- statement:
--   All named objects below are defined by OpenAI. Let $G$, $X$, $T$ be finite types and $e : G \simeq X \sqcup (X \sqcup T)$ an equivalence. Let $W, L$ be reals, $z : \texttt{Option}\ G \times X \to \mathbb{R}$, and `lower`, `width` $: G \to \mathbb{R}$ with $\mathrm{width}(g) \ne 0$ for all $g$. Suppose the two $X \times X$ matrices `fixedSpatialKernelBlock e W L z false` and `fixedSpatialKernelBlock e W L z true` have nonzero determinant (their $(x, i)$ entries are $\frac{L}{1+W}\, z(\mathrm{some}\ e^{-1}(\mathrm{inl}\ i), x)$ and $\frac{L}{1+W}\, z(\mathrm{some}\ e^{-1}(\mathrm{inr}(\mathrm{inl}\ i)), x)$ respectively). Let $\rho$ = `fixedSpatialKernelSliceDensity e W L z lower width h0 h1 hw`, a real function on $\mathbb{R}^X$; by OpenAI's theorem `fixedSpatialKernelSliceDensity_image_law` (a statement of this split, `fixedSpatialKernelSliceDensity_image_law_s2`), it is the density (with respect to Lebesgue measure) of the image of the uniform measure on $(0,1]^G$ under $t \mapsto \bigl(x \mapsto z(\mathrm{none}, x) + \frac{L}{1+W}\sum_g z(\mathrm{some}\ g, x)\,(\mathrm{lower}(g) + \mathrm{width}(g)\,t_g)\bigr)$.
--
--   Assume $0 \le W$, $0 \le L$, $|G|\cdot L \le W$, $|z(a)| \le 1$ for all $a$, and for all $g$: $0 \le \mathrm{lower}(g)$, $0 \le \mathrm{width}(g)$ and $\mathrm{lower}(g) + \mathrm{width}(g) \le 1$. Then for every $y \in \mathbb{R}^X$ with sup norm $\|y\| > 2$, $\rho(y) = 0$.
--
--   Lean: `OAI.Erdos3.fixedSpatialKernelSliceDensity_zero_of_norm_gt_two_s2`, which states OpenAI's `OAI.Erdos3.fixedSpatialKernelSliceDensity_zero_of_norm_gt_two` (in `lean/OAI/Combinatorics/Progressions/Linear/FixedSpatialKernelSliceDensity.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B100` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/FixedSpatialKernelSliceDensity.lean (declaration OAI.Erdos3.fixedSpatialKernelSliceDensity_zero_of_norm_gt_two)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100

section

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (lower width : G → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hw : ∀ g, width g ≠ 0)

local notation "density" => fixedSpatialKernelSliceDensity e W L z lower width h0 h1 hw

theorem fixedSpatialKernelSliceDensity_zero_of_norm_gt_two_s2
    (hW : 0 ≤ W) (hL : 0 ≤ L) (hsize : (Fintype.card G : ℝ) * L ≤ W)
    (hz : ∀ a, |z a| ≤ 1) (hl : ∀ g, 0 ≤ lower g)
    (hw0 : ∀ g, 0 ≤ width g) (hcontained : ∀ g, lower g + width g ≤ 1)
    (y : X → ℝ) (hy : 2 < ‖y‖) : density y = 0 := by
  sorry

end Erdos3

end

end OAI
end
