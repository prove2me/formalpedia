-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_joint_residue_comparison
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_joint_residue_comparison
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T00:08:44.859561+00:00
-- url     : https://prove2.me/theorems/162c8234-0fdd-4713-8814-bcf1712169d3
-- title:
--   Joint residue comparison for the fixed-path sliced sampler against continuous slices
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ (with decidable equality) and $X$; finite types $I_j$, natural numbers $n_j$, finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n`, finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$, bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$ (hypotheses $hR$, $h\sigma$); a layer-sampler scale `S : LayerSamplerScale B U basis R σ` with value $L = $ `S.value` $> 0$; and `u : PrincipalAxisTuples (allocatedShortAxis U basis L) (allocatedPrincipalSides B U basis S)` (with $\alpha$ = `Empty`), a choice of integer tuples on the short axes. Here `allocatedShortAxis U basis L` is the predicate on axes that holds at $\langle j, \mathrm{inr}\ i\rangle$ when `basisAxisScale (basis j) i` $\le L^{j+1}$ and fails on the axes $\langle j, \mathrm{inl}\ \_\rangle$; Active is the type of axes where it fails; $\mathrm{deg}\,a = j+1$ for an axis in layer $j$ (`layerSamplerDegree`); Input $= \Sigma_{a \in \mathrm{Active}}\, B_a \times \mathrm{Fin}(\mathrm{deg}\,a)$; Output $= \Sigma_{a \in \mathrm{Active}}\,\mathrm{Unit}$; Domain $= ((\Sigma_{x \in X}\,\mathrm{Unit} \sqcup \mathrm{Empty}) \to \mathbb R) \times (\mathrm{Output} \to \mathbb R)$; Sample is `CoefficientSamplerArrays I n` (for each $j$ a pair of a real array and an integer array indexed by coefficient exponents); and $W = $ `allocatedPhysicalRootBudget B U basis S (fun _ => 0)`, a real number defined by OpenAI.
--
--   Let $z : \mathrm{Option}\,G \times X \to \mathbb R$ with $|z(\mathrm{some}\,g, x)| \le 1$ for all $g, x$; $H_G : G \to \mathbb N$ with $0 < H_G(g)$; $c_G : G \to \mathbb Z$; $\mathrm{step}_G > 0$ natural with each progression $\{c_G(g) + \mathrm{step}_G\,k : 0 \le k < H_G(g)\}$ (`integerProgressionSupport`) contained in $[0, L)$; `sample : Sample` with `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)` for every $j$ (a predicate defined by OpenAI saying a certain mixed coefficient density is nonzero at the sample); a real $t > 0$ with $|\sigma_j| \le t$ for all $j$; $\mathrm{step}, H : \mathrm{Input} \to \mathbb N$ and $c : \mathrm{Input} \to \mathbb Z$ with $\mathrm{step}_j > 0$ and $H_j \ge 2$; a real $\delta > 0$; each progression $\{c_j + \mathrm{step}_j\,k : 0 \le k < H_j\}$ contained in $[0, L)$ and of cardinality at least $\delta L$; a natural number $q \ne 0$ with $q \le H_G(g)$ and $C\,q/H_G(g) < 1$ for all $g$, and $q \le H_j$ and $C\,q/H_j < 1$ for all $j$, where $C = $ `scalarCubeGridBoundaryConstant Empty`; a real $\varepsilon \ge 0$ with $\mathrm{step}_j / L \le \varepsilon$ for all $j$; $\delta \le 1$; an element $b_a \in B_a$ for every active $a$; a real $\eta > 0$; $A \in \mathbb R_{\ge 0}$ with `Real.smoothTransition` $A$-Lipschitz; the tail condition
--   $$|t| \cdot \texttt{polynomialMassC2Budget}\ |\mathrm{Input}|\ m\ 1 \le \texttt{slicedPrincipalC2Tolerance}\ |\mathrm{Input}|\ |\mathrm{Active}|\ m\ 1\ (\texttt{unitProfilePrincipalLowerBound}\ B)\ (\delta/2)\ A\ \eta$$
--   (explicit real expressions defined by OpenAI); and $\varphi : (G \to \mathbb Z/q) \to (\mathrm{Input} \to \mathbb Z/q) \to \mathrm{Domain} \to \mathbb C$ with $K_\varphi \ge 0$ such that each $\varphi(r_G, r)$ is $K_\varphi$-Lipschitz and $\|\varphi(r_G, r, y)\| \le 1$.
--
--   Put $\mathrm{lower}(a,p) = c_{\langle a,p\rangle}/L$, $\mathrm{width}(a,p) = \mathrm{step}_{\langle a,p\rangle}(H_{\langle a,p\rangle} - 1)/L$, $K = K_\varphi \cdot{}$`allocatedOriginalSampleFullSliceLip B U basis S t`; let kernel be the product over $g$ of the uniform weights on $x_g(\mathrm{none}) \in \{0, \dots, H_G(g) - 1\}$ (`integerScalarCubeWeights Empty`), active the analogous product over $j \in \mathrm{Input}$ with the $H_j$, and $\mathrm{embed}(x)_g = $ `containedProgressionCubeMap Empty L (HG g) stepG (cG g) …` $(x_g)$. Write $\mathbb E_\mu$ for the weighted mean $\sum_x \mu(x) f(x)$ (`complexMean`), $\kappa(s) = $ `fixedSpatialKernelMap W L z s` (the function $x \mapsto z(\mathrm{none}, x) + \frac{L}{1+W}\sum_g z(\mathrm{some}\,g, x)\,s_g$), $F(x, v) = $ `allocatedOriginalSampleFullSliceMap B U basis S (embed x) u (fun _ _ => 0) (fun _ _ => 1) sample v`, and $\Lambda(v) = $ `allocatedOriginalSampleLiftMap B U basis S lower width sample v`. Then
--   $$\Bigl\| \mathbb E_{\mathrm{kernel}}(x)\,\mathbb E_{\mathrm{active}}(v)\,\varphi\bigl(\overline{c_G + \mathrm{step}_G x_\cdot(\mathrm{none})},\ \overline{c + \mathrm{step}\, v_\cdot(\mathrm{none})},\ (\kappa(g \mapsto (c_G(g) + \mathrm{step}_G x_g(\mathrm{none}))/L),\ F(x, j \mapsto (c_j + \mathrm{step}_j v_j(\mathrm{none}))/L))\bigr) - \mathbb E_{r_A}\,\mathbb E_{r_G} \int_{(0,1]^G}\!\int_{(0,1]^{\mathrm{Input}}} \varphi\bigl(\overline{c_G} + \overline{\mathrm{step}_G}\, r_G,\ \overline{c} + \overline{\mathrm{step}}\, r_A,\ (\kappa(g \mapsto (c_G(g) + \mathrm{step}_G (H_G(g)-1) k_g)/L),\ \Lambda(v))\bigr)\,dv\,dk \Bigr\|$$
--   is at most
--   $$\Bigl(\sum_j \tfrac{q}{H_j} + 2\bigl((2C + 2K)\sum_j \tfrac{q}{H_j} + K\varepsilon\bigr) + 2\eta\Bigr) + (1 + 2(2C + K_\varphi) + K_\varphi)\sum_g \tfrac{q}{H_G(g)},$$
--   where bars denote reduction mod $q$, $r_A$ and $r_G$ range uniformly over $\mathrm{Input} \to \mathbb Z/q$ and $G \to \mathbb Z/q$, the integrals are against Lebesgue measure restricted to the boxes $(0,1]^G$ and $(0,1]^{\mathrm{Input}}$ (`unitBoxMeasure`), and $H_G(g) - 1$ is computed in $\mathbb N$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_joint_residue_comparison` in `lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedJointComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B149` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedJointComparison.lean#L37

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B172

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
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

variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => Spatial × (Output → ℝ)
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

include hR hσ in
theorem allocatedFixedPath_sliced_joint_residue_comparison
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1)
    (HG : G → ℕ) (hHG : ∀ g, 0 < HG g) (cG : G → ℤ)
    (stepG : ℕ) (hstepG : 0 < stepG)
    (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (sample : Sample)
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
    (q : ℕ) [NeZero q]
    (hsizeG : ∀ g, q ≤ HG g)
    (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1) (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (hδone : δ ≤ 1) (b : ∀ a : Active, B a.val)
    {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
    (φ : (G → ZMod q) → (Input → ZMod q) → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ rG r, LipschitzWith Kφ (φ rG r)) (hφone : ∀ rG r y, ‖φ rG r y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (HG g) (hHG g))
    let active := FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (H j)
      (by have := hH j; omega))
    let embed := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) g =>
      containedProgressionCubeMap Empty S.value (HG g) stepG (cG g) S.positive (hcontainedG g) (x g)
    ‖kernel.complexMean (fun x => active.complexMean (fun v =>
        φ (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
          (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
          (fixedSpatialKernelMap budget (S.value : ℝ) z
            (fun g => ((cG g : ℝ) + (stepG : ℝ) * (x g none : ℝ)) / S.value),
            allocatedOriginalSampleFullSliceMap B U basis S (embed x) u (fun _ _ => 0) (fun _ _ => 1)
              sample (fun j => ((c j : ℝ) + (step j : ℝ) * (v j none : ℝ)) / S.value)))) -
      (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun rA =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          ∫ k, ∫ v, φ (fun g => (cG g : ZMod q) + (stepG : ZMod q) * rG g)
            (fun j => (c j : ZMod q) + (step j : ZMod q) * rA j)
            (fixedSpatialKernelMap budget (S.value : ℝ) z
              (fun g => ((cG g : ℝ) + (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) * k g) / S.value),
              allocatedOriginalSampleLiftMap B U basis S lower width sample v)
            ∂unitBoxMeasure Input ∂unitBoxMeasure G))‖ ≤
      ((∑ j, (q : ℝ) / H j) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ j, (q : ℝ) / H j + K * ε) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ) + Kφ) * ∑ g, (q : ℝ) / HG g := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
