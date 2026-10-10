-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedOriginalSampleFullSlice_sliced_residue_complex_riemann
-- name    : OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleFullSlice_sliced_residue_complex_riemann
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T23:39:45.045651+00:00
-- url     : https://prove2.me/theorems/1356b4d2-1857-4546-beac-bdbc519b64f7
-- title:
--   Riemann-sum comparison for the full slice map along residue-conditioned progressions
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ and $I_j$, natural numbers $n_j$, finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$ (hypotheses $hR$, $h\sigma$); a layer-sampler scale `S : LayerSamplerScale B U basis R σ` with value $L = $ `S.value` $> 0$; a point $x : G \to $ `IntegerScalarCubeBox Empty L`; and `u : PrincipalAxisTuples (allocatedShortAxis U basis L) (allocatedPrincipalSides B U basis S)` (with $\alpha$ = `Empty`), a choice of integer tuples on the short axes. Here `allocatedShortAxis U basis L` is a predicate on axes defined by OpenAI, Active is the type of axes where it fails, $\mathrm{deg}\,a = j + 1$ for an axis in layer $j$, Input $= \Sigma_{a \in \mathrm{Active}}\, B_a \times \mathrm{Fin}(\mathrm{deg}\,a)$, Output $= \Sigma_{a \in \mathrm{Active}}\,\mathrm{Unit}$, and Sample is `CoefficientSamplerArrays I n`.
--
--   Let `sample : Sample` satisfy `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)` for every $j$; let $t > 0$ with $|\sigma_j| \le t$ for all $j$; let $\mathrm{step}, H, M : \mathrm{Input} \to \mathbb N$ and $c : \mathrm{Input} \to \mathbb Z$ with $\mathrm{step}_j > 0$ and $H_j \ge 2$; let $\delta > 0$ with each progression $\{c_j + \mathrm{step}_j\,k : 0 \le k < H_j\}$ (`integerProgressionSupport`) contained in $[0, L)$ and of cardinality at least $\delta L$; let $\mathrm{modulus}_j(i) \in \mathbb N$ and $\mathrm{residue}_j(i) \in \mathbb Z/\mathrm{modulus}_j(i)$ for $j \in \mathrm{Input}$ and $i \in \mathrm{Option}\,\mathrm{Empty}$, with $0 < \mathrm{modulus}_j(i) \le M_j$; assume $M_j \le H_j$ and $C\,M_j/H_j < 1$ for all $j$, where $C = $ `scalarCubeGridBoundaryConstant Empty`; let $\varepsilon \ge 0$ with $\mathrm{step}_j/L \le \varepsilon$ for all $j$; and let $\varphi : (\mathrm{Output} \to \mathbb R) \to \mathbb C$ be $K_\varphi$-Lipschitz with $\|\varphi\| \le 1$. Put $\mathrm{lower}(a,p) = c_{\langle a,p\rangle}/L$, $\mathrm{width}(a,p) = \mathrm{step}_{\langle a,p\rangle}(H_{\langle a,p\rangle} - 1)/L$ and $K = K_\varphi\cdot{}$`allocatedOriginalSampleFullSliceLip B U basis S t`, and write $F_{\ell, w} = $ `allocatedOriginalSampleFullSliceMap B U basis S x u ℓ w sample`. Let $\mu$ be the product over $j \in \mathrm{Input}$ of the probability weights `scalarCubeResidueWeights Empty (H j) (M j) … (modulus j) (residue j) …` on `IntegerScalarCubeBox Empty (H j)` (the uniform weights on the integer scalar cube conditioned on the residue set `scalarCubeResidueSet`). Then
--   $$\Bigl\| \sum_z \mu(z)\,\varphi\bigl(F_{0,1}(j \mapsto (c_j + \mathrm{step}_j\, z_j(\mathrm{none}))/L)\bigr) - \int_{(0,1]^{\mathrm{Input}}} \varphi(F_{\mathrm{lower},\mathrm{width}}(y))\,dy \Bigr\| \le 2\Bigl((2C + 2K)\sum_j \frac{M_j}{H_j} + K\varepsilon\Bigr),$$
--   where $F_{0,1}$ uses the constant lower ends $0$ and widths $1$, and the integral is against Lebesgue measure restricted to $(0,1]^{\mathrm{Input}}$ (`unitBoxMeasure`).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleFullSlice_sliced_residue_complex_riemann` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedOriginalSampleSlicedPerturbedRiemann.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B149` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedOriginalSampleSlicedPerturbedRiemann.lean#L34

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B172

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

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

include hR hσ in
theorem allocatedOriginalSampleFullSlice_sliced_residue_complex_riemann (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (step H M : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Input → Option Empty → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((M j : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (φ : (Output → ℝ) → ℂ) {Kφ : ℝ≥0}
    (hφ : LipschitzWith Kφ φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    ‖(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights Empty (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j)
        (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j))).complexMean
        (fun z => φ (allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))) -
      ∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
        ∂unitBoxMeasure Input‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
