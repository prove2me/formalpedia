-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastLawDensityPhysicalChartSource_haar_integral_unrestricted
-- name    : OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalChartSource_haar_integral_unrestricted
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T02:09:27.038224+00:00
-- url     : https://prove2.me/theorems/bd865ac9-56b1-4511-b94b-62a862438416
-- title:
--   Haar integral of the pushed-forward forecast chart source equals a raw-reference integral
-- statement:
--   Fix $m \in \mathbb N$, finite types $G$ and $X$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j, \sigma_j$, and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Write short for the predicate `allocatedShortAxis U basis S.value` on `LayerSamplerAxis I n`, Principal for `PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)`, and $\mathcal V$ for `LayerSamplerVariables G I n B`. Let law be `FiniteProbabilityWeights` (a probability vector) on Principal; density a real function on $\mathbb R^{\Sigma_{x : X} \mathrm{Unit} \oplus \mathrm{Empty}} \times \mathbb R^{\Sigma_{a : \{a \mid \neg\,\mathrm{short}\,a\}} \mathrm{Unit}}$; $A$ a type and $\mathrm{selected} : A \to \Sigma_j \mathrm{Fin}(n_j)$; sample in `CoefficientSamplerArrays I n` over $\mathcal V$; $x : G \to$ `IntegerScalarCubeBox Empty S.value`; $\Omega$ a finite type, $E^{\mathrm{out}}_j$ finite types, active a map from Principal to `FiniteProbabilityWeights Ω`, and $Y$ a map from Principal $\times\ \Omega$ to integer functions on `Sigma (AllocatedCongruenceRankOutput X Eout short)`; $N \ne 0$ a natural number; reals volume and $\tau$; $\mathrm{base} : X \to \mathbb Z$; $\mathrm{physicalN} : X \to \mathbb N$; and orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$. Write chartSource for `forecastLawDensityPhysicalChartSource B U basis S law density selected sample x active Y N volume base physicalN τ` (for each $u : X \to \mathbb Z$ a complex function on `MixedCoveredJetSource I (fun _ => Unit) Eout n N`) and region for `mixedCoveredJetRegion U o basis N (j () ↦ standardLatticeClosedQuarterBox (J j))` (with single-point row types and $E^{\mathrm{out}}$; `standardLatticeClosedQuarterBox (J j)` is $\{x : |x_i| \le 1/4\ \forall i\}$). Assume $R_j > 0$, $\sigma_j > 0$; `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)` for all $j$ (the sample lies where OpenAI's mixed coefficient density is nonzero); $\sigma_{(\mathrm{selected}\,a).1} \le 1$ for all $a$; every axis $a$ with short $a$ equals $((\mathrm{selected}\,i).1, \mathrm{inr}\,(\mathrm{selected}\,i).2)$ for some $i$; $\mathrm{density}(y) \ne 0$ implies $|y_2(a)| \le 3$ for all $a$; $r$ a nonnegative real with $0 < r$, $3 \le r$ and $|$`BoundedCoefficientExponent 𝒱 (j+1)`$| \le r$ for all $j$; $C_j \ge 0$ with $\|\chi_j^{-1}(v)\| \le C_j\|v\|$ for all $v$, where $\chi_j$ is the continuous linear equivalence `normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)`, and $C_j\bigl((|I_j|+1)(2rR_j)\bigr) \le 1/4$; ($h_b$) the $\mathbb Z$-span of the range of $\mathrm{basis}_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`; $bW_j$ a $\mathbb Z$-basis indexed by $E^{\mathrm{out}}_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`, which is assumed to be a $\mathbb Z$-lattice (`IsZLattice`); $\nu_j$ translation-invariant probability measures on the quotients of `euclideanSubspace (U j)` by these lattice sections; density measurable; $u : X \to \mathbb Z$; and test a measurable complex function on `EuclideanJetLayers U (fun _ => Unit)`. Let chart $=$ `mixedCoveredJetChart U o basis hb bW N` (single-point row types). Then
--   $$\int \texttt{restrictedComplexChartDensity}\ \mathrm{chart}\ \mathrm{region}\ 1\ (\mathrm{chartSource}\ u)\ y \cdot \mathrm{test}(y)\,d\textstyle\bigotimes_j \nu_j(y) = \texttt{coveredJetArrayScale}\ U \cdot \int \mathrm{chartSource}\ u\ z \cdot \mathrm{test}(\mathrm{chart}\ z)\,d\rho_N(z),$$
--   where `restrictedComplexChartDensity chart region 1 f` is the function equal to $f(z)$ at $\mathrm{chart}(z)$ for $z \in$ region and $0$ off the image, the measure on the left is the product of the $\nu_j$ (one copy for the single row of each layer), `coveredJetArrayScale U` is the real number $\prod_j \mathrm{covol}(\text{lattice section}_j)^{-1}$ (cast to $\mathbb C$), and $\rho_N =$ `mixedCoveredJetRawReference N` (product of OpenAI's mixed array reference measures with the uniform measure on the residue labels).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalChartSource_haar_integral_unrestricted` in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawOriginalNativeHaarJointMean.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B167` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawOriginalNativeHaarJointMean.lean#L161

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B167

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

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
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

end Erdos3.VectorPolynomial

end

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

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

theorem forecastLawDensityPhysicalChartSource_haar_integral_unrestricted
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
      (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hdensity : Measurable density) (u : X → ℤ)
    (test : EuclideanJetLayers U single → ℂ) (htest : Measurable test) :
    let chart := mixedCoveredJetChart (O := single) U o basis hb bW N
    (∫ y, restrictedComplexChartDensity chart region 1 (chartSource u) y * test y
      ∂Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))) =
      (coveredJetArrayScale (O := single) U : ℂ) *
        ∫ z, chartSource u z * test (chart z)
          ∂mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
