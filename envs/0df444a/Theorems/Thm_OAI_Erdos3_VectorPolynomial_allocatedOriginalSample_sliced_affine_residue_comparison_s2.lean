-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedOriginalSample_sliced_affine_residue_comparison_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_sliced_affine_residue_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:07:12.003988+00:00
-- url     : https://prove2.me/theorems/c11cb4d7-ee29-4e81-938a-3c50568fa492
-- title:
--   Comparing the progression-sampled original slice map with its continuous lift, jointly with residues
-- statement:
--   Let $m$ be a natural number and $G$ a finite type. For each $j < m$ let $I_j$ and $J_j$ be finite types, $n_j$ a natural number, $U_j$ a real subspace of $\mathbb{R}^{J_j}$ and $\mathrm{basis}_j$ a real basis, indexed by $\{0, \dots, n_j - 1\}$, of the orthogonal complement of the Euclidean subspace given by $U_j$. For each layer sampler axis $a$ (OpenAI's `LayerSamplerAxis I n`: pairs $(j, c)$ with $c \in I_j \sqcup \{0,\dots,n_j-1\}$; the axis $(j, c)$ has degree $j + 1$) let $B_a$ be a finite type. Let $R, \sigma : \{0,\dots,m-1\} \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$, and let $S$ be a layer sampler scale (OpenAI's `LayerSamplerScale B U basis R σ`, main field a positive natural number `S.value`). An axis is short if `allocatedShortAxis U basis S.value` holds for it (OpenAI: never for $c \in I_j$, and for $c = i < n_j$ when `basisAxisScale (basis j) i` $= \lceil 1/\lVert \mathrm{basis}_j(i)\rVert \rceil \le \texttt{S.value}^{j+1}$), and active otherwise. Let $\mathrm{Input}$ be the set of triples $(a, b, v)$ with $a$ active, $b \in B_a$, $v < \deg a$ (with $|\mathrm{Input}|$ elements), $\mathrm{Output}$ a copy of the set of active axes (with $|\mathrm{Active}|$ elements), and a sample an element of OpenAI's `CoefficientSamplerArrays I n` (for each $j$, a real array on $I_j$ and an integer array on $\{0,\dots,n_j-1\}$, indexed by the exponent vectors of total degree at most $j+1$ in the layer sampler variables). Let $x : G \to$ `IntegerScalarCubeBox Empty S.value` and let $u$ be a principal axis tuple (with $\alpha$ empty) for the short axes with the sides `allocatedPrincipalSides B U basis S` (OpenAI).
--
--   Let `sample` be a sample which is supported for every $j$ (OpenAI's `mixedArraySupported` with the allocated layer centers, widths and integer laws: the mixed coefficient density of the sample at layer $j$ is nonzero). Let $t > 0$ with $|\sigma_j| \le t$ for all $j$. Let $\mathrm{step}, H : \mathrm{Input} \to \mathbb{N}$ and $c : \mathrm{Input} \to \mathbb{Z}$ with $\mathrm{step}_\iota > 0$ and $H_\iota \ge 2$ for all $\iota$; let $\delta > 0$; assume each progression $P_\iota = \{c_\iota + \mathrm{step}_\iota k : 0 \le k < H_\iota\}$ lies in $\{0, \dots, \texttt{S.value} - 1\}$ and has at least $\delta\cdot\texttt{S.value}$ elements. Let $q$ be a nonzero natural number with $q \le H_\iota$ and $\Gamma \cdot q/H_\iota < 1$ for all $\iota$, where $\Gamma$ = `scalarCubeGridBoundaryConstant Empty` (an explicit constant of OpenAI; for the empty type it equals $4$). Let $\varepsilon \ge 0$ with $\mathrm{step}_\iota/\texttt{S.value} \le \varepsilon$ for all $\iota$, assume $\delta \le 1$, and let $b$ choose an element $b_a \in B_a$ for each active axis $a$. Let $\eta > 0$ and $A \ge 0$ with `Real.smoothTransition` $A$-Lipschitz, and assume
--   $$|t| \cdot \texttt{polynomialMassC2Budget}\ |\mathrm{Input}|\ m\ 1 \le \texttt{slicedPrincipalC2Tolerance}\ |\mathrm{Input}|\ |\mathrm{Active}|\ m\ 1\ (\texttt{unitProfilePrincipalLowerBound}\ B)\ (\delta/2)\ A\ \eta$$
--   (explicit quantities of OpenAI). Let $\varphi : (\mathrm{Input} \to \mathbb{Z}/q\mathbb{Z}) \to (\mathrm{Output} \to \mathbb{R}) \to \mathbb{C}$ with each $\varphi(r, \cdot)$ being $K_\varphi$-Lipschitz and $|\varphi(r, y)| \le 1$ for all $r, y$.
--
--   Put $\mathrm{lower}_\iota = c_\iota/\texttt{S.value}$, $\mathrm{width}_\iota = \mathrm{step}_\iota (H_\iota - 1)/\texttt{S.value}$, and $K = K_\varphi\cdot$`allocatedOriginalSampleFullSliceLip B U basis S t` (an explicit constant of OpenAI). Let $z = (z_\iota)$ be distributed according to the product over $\iota \in \mathrm{Input}$ of OpenAI's integer scalar cube weights `integerScalarCubeWeights Empty (H ι)` (each $z_\iota(\mathrm{none})$ is an integer coordinate), let $r$ be uniform on $(\mathbb{Z}/q\mathbb{Z})^{\mathrm{Input}}$ and $y$ distributed by Lebesgue measure on $(0,1]^{\mathrm{Input}}$ (OpenAI's `unitBoxMeasure`). Let $F$ = `allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1) sample` and $\Phi$ = `allocatedOriginalSampleLiftMap B U basis S lower width sample` be OpenAI's original-sample slice map and its lift (maps from $\mathbb{R}^{\mathrm{Input}}$ to $\mathbb{R}^{\mathrm{Output}}$). Then
--   $$\Bigl|\mathbb{E}_z\, \varphi\Bigl(\bigl(c_\iota + \mathrm{step}_\iota z_\iota(\mathrm{none}) \bmod q\bigr)_\iota,\ F\Bigl(\bigl(\tfrac{c_\iota + \mathrm{step}_\iota z_\iota(\mathrm{none})}{\texttt{S.value}}\bigr)_\iota\Bigr)\Bigr) - \mathbb{E}_r \int \varphi\bigl((c_\iota + \mathrm{step}_\iota r_\iota)_\iota,\ \Phi(y)\bigr)\, dy\Bigr|$$
--   $$\le \sum_\iota \frac{q}{H_\iota} + 2\Bigl((2\Gamma + 2K)\sum_\iota \frac{q}{H_\iota} + K\varepsilon\Bigr) + 2\eta.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_sliced_affine_residue_comparison_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_sliced_affine_residue_comparison` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedChildActiveResidueComparison.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B125`, `OAIE3v2B126` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedChildActiveResidueComparison.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_sliced_affine_residue_comparison)

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

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

include hR hσ in
theorem allocatedOriginalSample_sliced_affine_residue_comparison_s2 (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (q : ℕ) [NeZero q] (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (hδone : δ ≤ 1) (b : ∀ a : Active, B a.val)
    {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
    (φ : (Input → ZMod q) → (Output → ℝ) → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ r, LipschitzWith Kφ (φ r)) (hφone : ∀ r y, ‖φ r y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    ‖(FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (H j)
        (by have := hH j; omega))).complexMean
        (fun z => φ (fun j => ((c j + (step j : ℤ) * (z j none : ℤ) : ℤ) : ZMod q))
          (allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
            sample (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))) -
      𝔼 r : Input → ZMod q,
        ∫ y, φ (fun j => (c j : ZMod q) + (step j : ZMod q) * r j)
          (allocatedOriginalSampleLiftMap B U basis S lower width sample y)
          ∂unitBoxMeasure Input‖ ≤
      (∑ j, (q : ℝ) / H j) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ j, (q : ℝ) / H j + K * ε) + 2 * η) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
