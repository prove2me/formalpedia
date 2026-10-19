-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_fixedSpatialKernelSliceOriginalForecastDensity_bounds_s2
-- name    : OAI.Erdos3.VectorPolynomial.fixedSpatialKernelSliceOriginalForecastDensity_bounds_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:04:19.505976+00:00
-- url     : https://prove2.me/theorems/acf14f63-2f62-4c3e-b97e-f15143417234
-- title:
--   The sliced fixed spatial kernel original forecast density is bounded and Lipschitz with explicit constants
-- statement:
--   **Setting.** Let $m$ be a natural number, $G, X, T$ finite types, $I : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B$ a family of finite types indexed by `LayerSamplerAxis I n`, $J$ a family of finite types indexed by $\mathrm{Fin}\ m$, $U_j$ a real subspace of $J_j \to \mathbb{R}$, and $\mathrm{basis}_j$ a basis indexed by $\mathrm{Fin}\ (n\ j)$ of the orthogonal complement of `euclideanSubspace (U j)`. Let $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U basis R σ` (defined by OpenAI, with positive natural number `S.value`). Let $e : G \simeq X \oplus (X \oplus T)$ be an equivalence, $W, L$ real numbers, $z : \mathrm{Option}\ G \times X \to \mathbb{R}$, and $\mathrm{lower}_G, \mathrm{width}_G : G \to \mathbb{R}$. Suppose the two $X \times X$ matrices `fixedSpatialKernelBlock e W L z false` and `fixedSpatialKernelBlock e W L z true` have nonzero determinant (these are the matrices $(x, i) \mapsto \frac{L}{1+W}\, z(\mathrm{some}\ e^{-1}(\iota(i)), x)$ with $\iota(i) = \mathrm{inl}\ i$, respectively $\iota(i) = \mathrm{inr}(\mathrm{inl}\ i)$), and $\mathrm{width}_G(g) \ne 0$ for all $g$. Write "active" for the axes $a$ of `LayerSamplerAxis I n` that do not satisfy `allocatedShortAxis U basis S.value` (a predicate defined by OpenAI), and suppose $|B\ a| \ge 4$ for every active axis $a$. Let $\mathrm{lower}_P, \mathrm{width}_P$ assign to each active axis $a$ a real function on $B\ a \times \mathrm{Fin}\ (\texttt{layerSamplerDegree I n}\ a)$.
--
--   Let $\mathrm{frame}$ = `fixedSpatialKernelSliceFrame W L z lower_G width_G` (the frame equal to $z(\mathrm{none}, x) + \frac{L}{1+W}\sum_g z(\mathrm{some}\ g, x)\,\mathrm{lower}_G(g)$ at $(\mathrm{none}, x)$ and to $\mathrm{width}_G(g)\, z(\mathrm{some}\ g, x)$ at $(\mathrm{some}\ g, x)$). The corresponding blocks for $\mathrm{frame}$ are again nonsingular (by an OpenAI lemma), and $A_0, A_1$ denote the linear equivalences `fixedSpatialKernelBlockEquiv e W L frame false _` and `fixedSpatialKernelBlockEquiv e W L frame true _` they define.
--
--   **Hypotheses.** Let $\delta_P > 0$ be real with $\delta_P \le \mathrm{width}_P(a, p)$ and $0 \le \mathrm{lower}_P(a, p)$ for all active $a$ and all $p$. Let `sample : CoefficientSamplerArrays I n` satisfy, for every $j$, `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)` (the sample lies in the support of the layer's mixed coefficient density).
--
--   **Conclusion.** Let $f$ = `fixedSpatialKernelSliceOriginalForecastDensity B U basis S e W L z lower_G width_G h0 h1 hwG hB lower_P width_P sample`, a real-valued function defined by OpenAI. Then for every $y$, $0 \le f(y) \le$ `fixedSpatialOriginalForecastCap B A₁ hδP`, and $f$ is Lipschitz with constant `fixedSpatialOriginalForecastLip B A₀ A₁ hδP`; here the cap is the product of a density cap of the spatial block for $A_1$ (as used by OpenAI) with a lift cap depending on $B$ and $\delta_P$, and the Lipschitz constant is the corresponding product-rule combination, both explicit nonnegative reals defined by OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.fixedSpatialKernelSliceOriginalForecastDensity_bounds_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.fixedSpatialKernelSliceOriginalForecastDensity_bounds` (in `lean/OAI/Combinatorics/Progressions/Sampling/FixedSpatialKernelProgressionForecastIntegral.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B125` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/FixedSpatialKernelProgressionForecastIntegral.lean (declaration OAI.Erdos3.VectorPolynomial.fixedSpatialKernelSliceOriginalForecastDensity_bounds)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B125

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

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (lowerG widthG : G → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hwG : ∀ g, widthG g ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lowerP widthP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "frame" => fixedSpatialKernelSliceFrame W L z lowerG widthG
local notation "h0slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG false h0 hwG
local notation "h1slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG true h1 hwG
local notation "A₀" => fixedSpatialKernelBlockEquiv e W L frame false h0slice
local notation "A₁" => fixedSpatialKernelBlockEquiv e W L frame true h1slice

local notation "density" => fixedSpatialKernelSliceOriginalForecastDensity B U basis S e W L z
  lowerG widthG h0 h1 hwG hB lowerP widthP

variable {δP : ℝ} (hδP : 0 < δP)
  (hwP : ∀ a p, δP ≤ widthP a p) (hlP : ∀ a p, 0 ≤ lowerP a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelSliceOriginalForecastDensity_bounds_s2 :
    (∀ y, density sample y ∈ Set.Icc (0 : ℝ) (fixedSpatialOriginalForecastCap B A₁ hδP)) ∧
      LipschitzWith (fixedSpatialOriginalForecastLip B A₀ A₁ hδP) (density sample) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
