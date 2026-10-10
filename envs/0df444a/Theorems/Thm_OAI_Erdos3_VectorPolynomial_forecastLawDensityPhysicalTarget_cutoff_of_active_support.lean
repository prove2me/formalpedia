-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastLawDensityPhysicalTarget_cutoff_of_active_support
-- name    : OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalTarget_cutoff_of_active_support
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T02:43:24.582837+00:00
-- url     : https://prove2.me/theorems/5cf21522-7c00-4141-ad62-37a1e2cf105c
-- title:
--   Where the forecast physical target is nonzero, the buffered torus cutoff equals one
-- statement:
--   Fix $m \in \mathbb N$, finite types $G$ and $X$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j, \sigma_j$, and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Write short for the predicate `allocatedShortAxis U basis S.value` on `LayerSamplerAxis I n`, Principal for `PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)`, and $\mathcal V$ for `LayerSamplerVariables G I n B`. Let law be `FiniteProbabilityWeights` (a probability vector) on Principal; density a real function on $\mathbb R^{\Sigma_{x : X} \mathrm{Unit} \oplus \mathrm{Empty}} \times \mathbb R^{\Sigma_{a : \{a \mid \neg\,\mathrm{short}\,a\}} \mathrm{Unit}}$; $A$ a type and $\mathrm{selected} : A \to \Sigma_j \mathrm{Fin}(n_j)$; sample in `CoefficientSamplerArrays I n` over $\mathcal V$; $x : G \to$ `IntegerScalarCubeBox Empty S.value`; $\Omega$ a finite type, $E^{\mathrm{out}}_j$ finite types, active a map from Principal to `FiniteProbabilityWeights Ω`, and $Y$ a map from Principal $\times\ \Omega$ to integer functions on `Sigma (AllocatedCongruenceRankOutput X Eout short)`; $N \ne 0$ a natural number; reals volume and $\tau$; $\mathrm{base} : X \to \mathbb Z$; $\mathrm{physicalN} : X \to \mathbb N$; orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; ($h_b$) the hypothesis that the $\mathbb Z$-span of the range of $\mathrm{basis}_j$ is `projectedIntegerLattice (euclideanSubspace (U j))` for every $j$; and $bW_j$ a $\mathbb Z$-basis indexed by $E^{\mathrm{out}}_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (the integer lattice intersected with that subspace). Write target for `forecastLawDensityPhysicalTarget B U basis S law density selected sample x active Y N volume base physicalN τ o hb bW` (given vector polynomials, the coefficient hypothesis and $u : X \to \mathbb Z$, a complex number). Assume $R_j > 0$, $\sigma_j > 0$; `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)` for all $j$ (the sample lies where OpenAI's mixed coefficient density is nonzero); $\sigma_{(\mathrm{selected}\,a).1} \le 1$ for all $a$; every axis $a$ with short $a$ equals $((\mathrm{selected}\,i).1, \mathrm{inr}\,(\mathrm{selected}\,i).2)$ for some $i$; $\mathrm{density}(y) \ne 0$ implies $|y_2(a)| \le 3$ for all $a$; $r$ a nonnegative real with $0 < r$, $3 \le r$ and $|$`BoundedCoefficientExponent 𝒱 (j+1)`$| \le r$ for all $j$; and $C_j \ge 0$ with $\|\chi_j^{-1}(v)\| \le C_j\|v\|$ for all $v$, where $\chi_j$ is the continuous linear equivalence `normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)`, and $C_j\bigl((|I_j|+1)(2rR_j)\bigr) \le 1/4$. Let $\mathrm{poly}_j$ be vector polynomials in variables $X$ over $\mathbb R$ with values in $\mathbb R^{J_j}$ all of whose coefficients lie in $U_j$ ($h_{\mathrm{poly}}$), and $u : X \to \mathbb Z$ with `target poly hpoly u` $\ne 0$. Then `allocatedBufferedTorusCutoff U basis o r hr` (with $R$), a real function on $(\mathbb R/\mathbb Z)^{\Sigma_j\, \mathrm{Unit} \times J_j}$, takes the value $1$ at the point $(j, (), k) \mapsto \mathrm{poly}_j(u)_k \bmod 1$, where $\mathrm{poly}_j(u) \in \mathbb R^{J_j}$ is the evaluation `eval u (poly j)` at $u$ cast to reals.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalTarget_cutoff_of_active_support` in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawNativeRawJointMean.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B167` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawNativeRawJointMean.lean#L190

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

local notation "deckSource" => forecastLawDensityPhysicalDeckSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

local notation "target" => forecastLawDensityPhysicalTarget B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW

theorem forecastLawDensityPhysicalTarget_cutoff_of_active_support
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
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
    (hnonzero : target poly hpoly u ≠ 0) :
    allocatedBufferedTorusCutoff (R := R) U basis o r hr
      (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) = 1 := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
