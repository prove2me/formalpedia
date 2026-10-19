-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_fixedSpatialKernelSliceOriginalForecastDensity_zero_of_norm_gt_two_s2
-- name    : OAI.Erdos3.VectorPolynomial.fixedSpatialKernelSliceOriginalForecastDensity_zero_of_norm_gt_two_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:38:10.123326+00:00
-- url     : https://prove2.me/theorems/94450c94-bdf8-435e-943d-7f3c3c218e7a
-- title:
--   The sliced fixed-kernel forecast density vanishes outside the ball of radius 2
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$, $X$, $T$; finite types $I_j$, natural numbers $n_j$, finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$; a layer-sampler scale `S : LayerSamplerScale B U basis R σ`; with Active the type of axes on which the predicate `allocatedShortAxis U basis S.value` (defined by OpenAI) fails, $\mathrm{deg}\,a = j+1$ for an axis in layer $j$, Output $= \Sigma_{a \in \mathrm{Active}}\,\mathrm{Unit}$ and Domain $= ((\Sigma_{x \in X}\,\mathrm{Unit} \sqcup \mathrm{Empty}) \to \mathbb R) \times (\mathrm{Output} \to \mathbb R)$. Further fix an equivalence $e : G \simeq X \sqcup (X \sqcup T)$, reals $W, L$, a function $z : \mathrm{Option}\,G \times X \to \mathbb R$, functions $\mathrm{lower}_G, \mathrm{width}_G : G \to \mathbb R$, the hypotheses that the matrices `fixedSpatialKernelBlock e W L z false` and `fixedSpatialKernelBlock e W L z true` have nonzero determinant and that $\mathrm{width}_G(g) \ne 0$ for all $g$, the hypothesis $4 \le |B_a|$ for every active $a$, real functions $\mathrm{lower}_P, \mathrm{width}_P$ on pairs $(a, p)$ with $a$ active and $p \in B_a \times \mathrm{Fin}(\mathrm{deg}\,a)$, a real $\delta_P > 0$ with $\delta_P \le \mathrm{width}_P(a,p)$ and $0 \le \mathrm{lower}_P(a,p)$ for all $a, p$, and `sample : CoefficientSamplerArrays I n` satisfying `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)` for every $j$. Let $\rho = $ `fixedSpatialKernelSliceOriginalForecastDensity B U basis S e W L z lowerG widthG h0 h1 hwG hB lowerP widthP sample`, a real function on Domain defined by OpenAI from the slice frame `fixedSpatialKernelSliceFrame W L z lowerG widthG` and the sample's restricted profile noise. Assume moreover: $|\mathrm{lower}_P(a,p)| + |\mathrm{width}_P(a,p)| \le 1$ for all $a, p$; $0 \le W$; $0 \le L$; $|G| \cdot L \le W$; $|z(a)| \le 1$ for all $a$; $0 \le \mathrm{lower}_G(g)$, $0 \le \mathrm{width}_G(g)$ and $\mathrm{lower}_G(g) + \mathrm{width}_G(g) \le 1$ for all $g$. Then for every $y \in$ Domain with $\|y\| > 2$ (sup norm on the product), $\rho(y) = 0$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.fixedSpatialKernelSliceOriginalForecastDensity_zero_of_norm_gt_two_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.fixedSpatialKernelSliceOriginalForecastDensity_zero_of_norm_gt_two` (in `lean/OAI/Combinatorics/Progressions/Sampling/FixedSpatialKernelProgressionForecastIntegral.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B105` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/FixedSpatialKernelProgressionForecastIntegral.lean (declaration OAI.Erdos3.VectorPolynomial.fixedSpatialKernelSliceOriginalForecastDensity_zero_of_norm_gt_two)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B105

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (lowerG widthG : G → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hwG : ∀ g, widthG g ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lowerP widthP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "density" => fixedSpatialKernelSliceOriginalForecastDensity B U basis S e W L z
  lowerG widthG h0 h1 hwG hB lowerP widthP

variable {δP : ℝ} (hδP : 0 < δP)
  (hwP : ∀ a p, δP ≤ widthP a p) (hlP : ∀ a p, 0 ≤ lowerP a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelSliceOriginalForecastDensity_zero_of_norm_gt_two_s2
    (hwidthP : ∀ a p, |lowerP a p| + |widthP a p| ≤ 1)
    (hW : 0 ≤ W) (hL : 0 ≤ L) (hsize : (Fintype.card G : ℝ) * L ≤ W)
    (hz : ∀ a, |z a| ≤ 1) (hlG : ∀ g, 0 ≤ lowerG g) (hwG0 : ∀ g, 0 ≤ widthG g)
    (hcontained : ∀ g, lowerG g + widthG g ≤ 1)
    (y : Domain) (hy : 2 < ‖y‖) : density sample y = 0 := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
