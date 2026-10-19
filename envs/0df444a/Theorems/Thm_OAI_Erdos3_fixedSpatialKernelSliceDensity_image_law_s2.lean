-- Prove2me | Theorems.Thm_OAI_Erdos3_fixedSpatialKernelSliceDensity_image_law_s2
-- name    : OAI.Erdos3.fixedSpatialKernelSliceDensity_image_law_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:39:29.823427+00:00
-- url     : https://prove2.me/theorems/81b5613a-652e-4156-b3ed-2704e02b6b59
-- title:
--   The image of the uniform law on the unit box under the fixed spatial kernel map has the fixed spatial kernel slice density
-- statement:
--   Let $G, X, T$ be finite types and $e : G \simeq X \sqcup (X \sqcup T)$ a bijection. Let $W, L$ be real numbers, $z : \mathrm{Option}\,G \times X \to \mathbb{R}$, and $\mathrm{lower}, \mathrm{width} : G \to \mathbb{R}$ with $\mathrm{width}(g) \ne 0$ for all $g$. For $\mathrm{second} \in \{\mathrm{false}, \mathrm{true}\}$ let $M_{\mathrm{second}}$ = `fixedSpatialKernelBlock e W L z second`, the $X \times X$ real matrix with entries $(M_{\mathrm{second}})_{x,i} = \frac{L}{1+W}\, z(\mathrm{some}\ e^{-1}(\iota_{\mathrm{second}}(i)), x)$, where $\iota_{\mathrm{false}}(i) = \mathrm{inl}\, i$ and $\iota_{\mathrm{true}}(i) = \mathrm{inr}(\mathrm{inl}\, i)$ (defined by OpenAI). Assume $\det M_{\mathrm{false}} \ne 0$ and $\det M_{\mathrm{true}} \ne 0$.
--
--   For $t \in \mathbb{R}^G$ let $\Phi(t) \in \mathbb{R}^X$ be given by
--   $$\Phi(t)_x = z(\mathrm{none}, x) + \frac{L}{1+W} \sum_{g \in G} z(\mathrm{some}\ g, x)\,\bigl(\mathrm{lower}(g) + \mathrm{width}(g)\, t_g\bigr)$$
--   (this is `fixedSpatialKernelMap W L z (fun g => lower g + width g * t g)` evaluated at the index $(x, \mathrm{inl}\ ())$, defined by OpenAI). Then the push-forward under $\Phi$ of the uniform probability measure on the unit box $(0,1]^G$ (`unitBoxMeasure G`, Lebesgue measure restricted to the box) equals the measure on $\mathbb{R}^X$ with density $y \mapsto \max(\rho(y), 0)$ with respect to Lebesgue measure (`realDensityMeasure volume ρ`), where $\rho$ = `fixedSpatialKernelSliceDensity e W L z lower width _ _ _` is the real-valued function on $\mathbb{R}^X$ defined by OpenAI (the fixed spatial kernel density of the affinely reparametrized frame `fixedSpatialKernelSliceFrame W L z lower width`, whose two blocks are invertible by the hypotheses above).
--
--   Lean: `OAI.Erdos3.fixedSpatialKernelSliceDensity_image_law_s2`, which states OpenAI's `OAI.Erdos3.fixedSpatialKernelSliceDensity_image_law` (in `lean/OAI/Combinatorics/Progressions/Linear/FixedSpatialKernelSliceDensity.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B100` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/FixedSpatialKernelSliceDensity.lean (declaration OAI.Erdos3.fixedSpatialKernelSliceDensity_image_law)

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
local notation "frame" => fixedSpatialKernelSliceFrame W L z lower width
local notation "h0slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lower width false h0 hw
local notation "h1slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lower width true h1 hw

local notation "density" => fixedSpatialKernelSliceDensity e W L z lower width h0 h1 hw

theorem fixedSpatialKernelSliceDensity_image_law_s2 :
    (unitBoxMeasure G).map (fun t x =>
      fixedSpatialKernelMap W L z (fun g => lower g + width g * t g) ⟨x, .inl ()⟩) =
      realDensityMeasure volume density := by
  sorry

end Erdos3

end

end OAI
end
