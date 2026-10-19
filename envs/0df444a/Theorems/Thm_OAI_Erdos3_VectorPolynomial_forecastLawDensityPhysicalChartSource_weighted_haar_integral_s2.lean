-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastLawDensityPhysicalChartSource_weighted_haar_integral_s2
-- name    : OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalChartSource_weighted_haar_integral_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:51:42.373551+00:00
-- url     : https://prove2.me/theorems/695ef802-fee7-4f7b-a3a6-ae7395ae2808
-- title:
--   Change of variables from Haar measure on the jet-layer tori to the raw mixed covered reference measure for the forecast-law physical chart source
-- statement:
--   **Setting.** Let $m \in \mathbb{N}$; let $G$ and $X$ be finite types; let $I_j$ ($j \in \mathrm{Fin}\,m$) be finite types, $n : \mathrm{Fin}\,m \to \mathbb{N}$, and $B_a$ finite types indexed by the sampler axes $a$ in `LayerSamplerAxis I n`; let $J_j$ be finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, and $\mathrm{basis}_j$ a basis, indexed by $\mathrm{Fin}(n_j)$, of the orthogonal complement of $U_j$; let $R, \sigma : \mathrm{Fin}\,m \to \mathbb{R}$ and $S$ a `LayerSamplerScale B U basis R σ` (defined by OpenAI). Let `law` be a finite probability law on `PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)`; let `density` be a real-valued function of a pair of real vectors (indexed by $\Sigma_{x \in X} (\mathrm{Unit} \sqcup \emptyset)$, and by the axes $a$ that are not short axes in the sense of `allocatedShortAxis U basis S.value`); let $A$ be a type and $\mathrm{selected} : A \to \Sigma_j \mathrm{Fin}(n_j)$; let `sample` be a `CoefficientSamplerArrays` and $x : G \to$ `IntegerScalarCubeBox Empty S.value`; let $\Omega$ be a finite type, $E^{\mathrm{out}}_j$ finite types, `active` a map from principal integer tuples to finite probability laws on $\Omega$, and $Y$ a map from (principal integer tuple, $\omega \in \Omega$, congruence rank output index) to $\mathbb{Z}$; let $N$ be a positive natural number, `volume` a real, `base` $: X \to \mathbb{Z}$, `physicalN` $: X \to \mathbb{N}$, $\tau \in \mathbb{R}$. Let $o_j$ be an orthonormal basis of $U_j$ indexed by $I_j$; assume (hypothesis $h_b$) that the $\mathbb{Z}$-span of $\mathrm{basis}_j$ is the projected integer lattice `projectedIntegerLattice` of $U_j$; let $bW_j$ be a $\mathbb{Z}$-basis, indexed by $E^{\mathrm{out}}_j$, of the lattice $\Gamma_j$ = the section of $\mathbb{Z}^{J_j}$ by $U_j$, and assume each $\Gamma_j$ is a full lattice in $U_j$. Let $\nu_j$ be a left-invariant (Haar) probability measure on the torus $U_j / \Gamma_j$.
--
--   With $\mathrm{single}_j = \mathrm{Unit}$, let $\mathrm{chart}$ = `mixedCoveredJetChart U o basis h_b bW N` (from `MixedCoveredJetSource` to `EuclideanJetLayers U single`), $\mathrm{region}$ = `mixedCoveredJetRegion U o basis N Ω₀` with $\Omega_0$ the closed quarter boxes $\{v : |v_i| \le 1/4\}$, $\mathrm{haar}$ = the product measure $\prod_j \nu_j$ on `EuclideanJetLayers U single`, and $\mathrm{raw}$ = `mixedCoveredJetRawReference N` (a product of a reference measure on arrays and the uniform law on residues modulo $N$; defined by OpenAI). Write $F_u$ for `forecastLawDensityPhysicalChartSource B U basis S law density selected sample x active Y N volume base physicalN τ u`, a complex-valued function on `MixedCoveredJetSource` defined by OpenAI.
--
--   **Statement.** Assume `density` is measurable. Let $u : X \to \mathbb{Z}$ and let $\mathrm{test} : \texttt{EuclideanJetLayers U single} \to \mathbb{C}$ be measurable. Then
--   $$\int \texttt{restrictedComplexChartDensity}\ \mathrm{chart}\ \mathrm{region}\ 1\ F_u\ (y) \cdot \mathrm{test}(y)\, d\mathrm{haar}(y) = \kappa \cdot \int_{\mathrm{region}} F_u(z) \cdot \mathrm{test}(\mathrm{chart}\ z)\, d\mathrm{raw}(z),$$
--   where `restrictedComplexChartDensity q S c f` (defined by OpenAI) is the function $y \mapsto c \cdot f(z)$ if $y = q(z)$ for some $z \in S$ (chosen arbitrarily if there are several) and $0$ otherwise, and $\kappa$ = `coveredJetArrayScale U` $= \prod_j \operatorname{covol}(\Gamma_j)^{-1}$ (for one row per layer).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalChartSource_weighted_haar_integral_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalChartSource_weighted_haar_integral` (in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawOriginalNativeHaarJointMean.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B199` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawOriginalNativeHaarJointMean.lean (declaration OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalChartSource_weighted_haar_integral)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B199

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N

theorem forecastLawDensityPhysicalChartSource_weighted_haar_integral_s2
    (hdensity : Measurable density) (u : X → ℤ)
    (test : EuclideanJetLayers U single → ℂ) (htest : Measurable test) :
    (∫ y, restrictedComplexChartDensity chart region 1 (chartSource u) y * test y ∂haar) =
      (coveredJetArrayScale (O := single) U : ℂ) *
        ∫ z in region, chartSource u z * test (chart z) ∂raw := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
