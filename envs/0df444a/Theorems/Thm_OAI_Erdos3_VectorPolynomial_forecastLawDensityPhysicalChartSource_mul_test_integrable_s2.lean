-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastLawDensityPhysicalChartSource_mul_test_integrable_s2
-- name    : OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalChartSource_mul_test_integrable_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:46:01.547992+00:00
-- url     : https://prove2.me/theorems/090efb2a-443d-41d8-bac3-97bfe04e8e12
-- title:
--   The forecast-law physical chart source times a bounded measurable test of the chart is integrable for the raw covered-jet reference
-- statement:
--   All named objects below are defined by OpenAI.
--
--   **Data.** Let $m$ be a natural number, $G, X$ finite types, $I_j$ ($j<m$) finite types, $n : \mathrm{Fin}(m)\to\mathbb{N}$, $B_a$ finite types indexed by `LayerSamplerAxis I n` $= \Sigma_j (I_j \sqcup \mathrm{Fin}(n_j))$, $J_j$ finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, `basis j` bases (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, $R, \sigma : \mathrm{Fin}(m)\to\mathbb{R}$, and `S : LayerSamplerScale B U basis R σ`. Write `short` = `allocatedShortAxis U basis S.value` (true exactly on the integer axes $(j, \mathrm{inr}\ i)$ with `basisAxisScale (basis j) i` $\le \texttt{S.value}^{j+1}$). Let `law` be finite probability weights on `PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)`; `density` a real function on pairs (a real array indexed by $\Sigma_{x \in X}(\mathrm{Unit} \sqcup \mathrm{Empty})$, a real array indexed by the non-short axes); `selected : A → Σ j, Fin (n j)` for a type $A$; `sample : CoefficientSamplerArrays I n` (over `LayerSamplerVariables G I n B`); $x : G \to$ `IntegerScalarCubeBox Empty S.value`; a finite type $\Omega$ and finite types $E^{\mathrm{out}}_j$; `active` assigning finite probability weights on $\Omega$ to each tuple; `Y` assigning to each tuple and $\omega \in \Omega$ an integer array on `Sigma (AllocatedCongruenceRankOutput X Eout short)`; a natural number $N \ge 1$; a real `volume`; `base : X → ℤ`; `physicalN : X → ℕ`; a real $\tau$; and orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$. Let `chartSource` = `forecastLawDensityPhysicalChartSource B U basis S law density selected sample x active Y N volume base physicalN τ`.
--
--   **Hypotheses.** $R_j > 0$ and $\sigma_j > 0$ for all $j$; for every $j$, `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)`; $\sigma_{(\mathrm{selected}\ a).1} \le 1$ for every $a \in A$; every short axis $a$ equals $((\mathrm{selected}\ i).1, \mathrm{inr}\ (\mathrm{selected}\ i).2)$ for some $i \in A$; whenever $\mathrm{density}(y) \ne 0$, every entry of the second component of $y$ has absolute value at most $3$; $r \in \mathbb{R}_{\ge 0}$ with $r > 0$ and $3 \le r$; $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| \le r$ for all $j$; $C : \mathrm{Fin}(m)\to\mathbb{R}$ with $C_j \ge 0$ and $\|\Phi_j^{-1}(v)\| \le C_j\|v\|$ for all $j, v$, where $\Phi_j$ = `normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)`; $C_j((|I_j|+1)(2rR_j)) \le 1/4$ for all $j$; `hb`: the $\mathbb{Z}$-span of each `basis j` is the projected integer lattice; `bW j` are $\mathbb{Z}$-bases (indexed by $E^{\mathrm{out}}_j$) of the lattice section of $\mathbb{Z}^{J_j}$ in `euclideanSubspace (U j)`; `density` is continuous.
--
--   **Statement.** For every $u : X \to \mathbb{Z}$ and every measurable `test : EuclideanJetLayers U (fun _ => Unit) → ℂ` bounded in norm by some real `testCap`, the function
--   $$z \mapsto \texttt{chartSource}\ u\ z\cdot \texttt{test}\bigl(\texttt{mixedCoveredJetChart U o basis hb bW N}\ z\bigr)$$
--   on `MixedCoveredJetSource I (fun _ => Unit) Eout n N` is integrable with respect to `mixedCoveredJetRawReference N` (the product of OpenAI's mixed array reference measures with the uniform measure on the residue arrays mod $N$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalChartSource_mul_test_integrable_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalChartSource_mul_test_integrable` (in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawOriginalNativeHaarJointMean.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B199` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawOriginalNativeHaarJointMean.lean (declaration OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalChartSource_mul_test_integrable)

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

local notation "short" => allocatedShortAxis (I := I) U basis S.value
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

local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

theorem forecastLawDensityPhysicalChartSource_mul_test_integrable_s2
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
    (hdensity : Continuous density) (u : X → ℤ)
    (test : EuclideanJetLayers U single → ℂ) (htest : Measurable test)
    {testCap : ℝ} (hbound : ∀ y, ‖test y‖ ≤ testCap) :
    Integrable (fun z => chartSource u z * test (mixedCoveredJetChart U o basis hb bW N z))
      (mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
