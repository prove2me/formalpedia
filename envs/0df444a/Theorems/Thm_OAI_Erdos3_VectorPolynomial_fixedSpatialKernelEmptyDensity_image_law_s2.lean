-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_fixedSpatialKernelEmptyDensity_image_law_s2
-- name    : OAI.Erdos3.VectorPolynomial.fixedSpatialKernelEmptyDensity_image_law_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:29:13.065978+00:00
-- url     : https://prove2.me/theorems/3c0fc2e3-251f-462e-94ed-586945f133b1
-- title:
--   The image of the uniform unit-box law under the fixed spatial kernel map has the fixed spatial kernel density
-- statement:
--   Let $G, X, T$ be finite types ($X$ with decidable equality) and $e : G \simeq X \sqcup (X \sqcup T)$ a bijection. Let $W, L$ be real numbers and $z : \mathrm{Option}\,G \times X \to \mathbb{R}$. Put $\lambda = L/(1+W)$. For a Boolean `second`, `fixedSpatialKernelBlock e W L z second` is the real $X \times X$ matrix (defined by OpenAI) whose $(x, i)$ entry is $\lambda \cdot z(e^{-1}(i'), x)$, where $i'$ is the copy of $i$ in the first summand $X$ when `second` is false and in the second summand $X$ when `second` is true. Assume both of these matrices have nonzero determinant.
--
--   Let $\mathcal{U}_G$ be OpenAI's `unitBoxMeasure G`, Lebesgue measure on $\mathbb{R}^{G}$ restricted to the box $(0,1]^{G}$. Let `fixedSpatialKernelMap W L z` be the map (OpenAI) sending $t \in \mathbb{R}^{G}$ to the vector indexed by $X$ (formally by the pairs $(x, \star)$ of the type $\Sigma_{x \in X}(\mathrm{Unit} \sqcup \mathrm{Empty})$) with entries
--   $$z(\mathrm{none}, x) + \lambda \sum_{g \in G} z(g, x)\, t_g.$$
--   Let $\rho$ = `fixedSpatialKernelDensity e W L z h0 h1`, a function $\mathbb{R}^{X} \to \mathbb{R}$ defined by OpenAI: the mixture, over $t$ distributed by $\mathcal{U}_T$, of the translates by $z(\mathrm{none}, \cdot) + \lambda \sum_{\tau \in T} z(e^{-1}(\tau), \cdot)\, t_\tau$ of a two-box difference density built from the invertible linear maps given by the two block matrices; and let $\rho'$ = `fixedSpatialEmptyDensity ρ` be $\rho$ transported to the index type $\Sigma_{x \in X}(\mathrm{Unit} \sqcup \mathrm{Empty})$ by the identification $v \mapsto (x \mapsto v(x, \star))$. Then the pushforward of $\mathcal{U}_G$ under `fixedSpatialKernelMap W L z` equals the measure with density $\max(\rho', 0)$ with respect to Lebesgue measure (OpenAI's `realDensityMeasure volume ρ'`, which uses the density $x \mapsto \mathrm{ENNReal.ofReal}(\rho'(x))$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.fixedSpatialKernelEmptyDensity_image_law_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.fixedSpatialKernelEmptyDensity_image_law` (in `lean/OAI/Combinatorics/Progressions/Sampling/FixedSpatialKernelProgressionForecastIntegral.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B035`, `OAIE3v2B074` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/FixedSpatialKernelProgressionForecastIntegral.lean (declaration OAI.Erdos3.VectorPolynomial.fixedSpatialKernelEmptyDensity_image_law)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B035
import Definitions.Def_OAIE3v2B074

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
local notation "spatial" => fixedSpatialEmptyDensity (fixedSpatialKernelDensity e W L z h0 h1)

variable {δ : ℝ}
  (hδ : 0 < δ)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

omit hR hσ in
theorem fixedSpatialKernelEmptyDensity_image_law_s2 :
    (unitBoxMeasure G).map (fixedSpatialKernelMap W L z) = realDensityMeasure volume spatial := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
