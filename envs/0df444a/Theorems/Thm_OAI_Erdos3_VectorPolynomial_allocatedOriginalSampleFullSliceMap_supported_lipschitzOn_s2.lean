-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedOriginalSampleFullSliceMap_supported_lipschitzOn_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleFullSliceMap_supported_lipschitzOn_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:11:54.480988+00:00
-- url     : https://prove2.me/theorems/e05dee2a-fa4b-4530-88a4-e2b7e2458334
-- title:
--   The full slice map of a supported sample is Lipschitz on the closed unit ball
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ and $I_j$, natural numbers $n_j$, finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$ (hypotheses $hR$, $h\sigma$); a layer-sampler scale `S : LayerSamplerScale B U basis R σ` with value $L = $ `S.value`; a point $x : G \to $ `IntegerScalarCubeBox Empty L`; and `u : PrincipalAxisTuples (allocatedShortAxis U basis L) (allocatedPrincipalSides B U basis S)` (with $\alpha$ = `Empty`), a choice of integer tuples on the short axes. Here `allocatedShortAxis U basis L` is a predicate on axes defined by OpenAI, Active is the type of axes where it fails, $\mathrm{deg}\,a = j + 1$ for an axis in layer $j$, Input $= \Sigma_{a \in \mathrm{Active}}\, B_a \times \mathrm{Fin}(\mathrm{deg}\,a)$, Output $= \Sigma_{a \in \mathrm{Active}}\,\mathrm{Unit}$, and Sample is `CoefficientSamplerArrays I n`. Let `sample : Sample` satisfy `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)` for every $j$ (a predicate defined by OpenAI saying a certain mixed coefficient density is nonzero at the sample), let $\mathrm{lower}, \mathrm{width}$ assign a real number to each active $a$ and each $p \in B_a \times \mathrm{Fin}(\mathrm{deg}\,a)$ with $|\mathrm{lower}(a,p)| + |\mathrm{width}(a,p)| \le 1$, and let $t > 0$ be real with $|\sigma_j| \le t$ for all $j$. Then the map `allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample` $: (\mathrm{Input} \to \mathbb R) \to (\mathrm{Output} \to \mathbb R)$ is Lipschitz with constant `allocatedOriginalSampleFullSliceLip B U basis S t` $= (1 + |t|)\cdot{}$`allocatedOriginalSampleLiftLip B U basis S` on the closed ball of radius $1$ about $0$ (sup norm).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleFullSliceMap_supported_lipschitzOn_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleFullSliceMap_supported_lipschitzOn` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedOriginalSampleFullSliceLipschitz.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B125`, `OAIE3v2B126` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedOriginalSampleFullSliceLipschitz.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleFullSliceMap_supported_lipschitzOn)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B125
import Definitions.Def_OAIE3v2B126

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

theorem allocatedOriginalSampleFullSliceMap_supported_lipschitzOn_s2
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t) :
    LipschitzOnWith (allocatedOriginalSampleFullSliceLip B U basis S t)
      (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample)
      (Metric.closedBall 0 1) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
