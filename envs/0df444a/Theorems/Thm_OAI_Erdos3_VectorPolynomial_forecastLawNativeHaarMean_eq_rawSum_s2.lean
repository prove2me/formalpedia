-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastLawNativeHaarMean_eq_rawSum_s2
-- name    : OAI.Erdos3.VectorPolynomial.forecastLawNativeHaarMean_eq_rawSum_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:59:14.533089+00:00
-- url     : https://prove2.me/theorems/17a7a996-f400-4169-8fb6-5800ad7d79e3
-- title:
--   The Haar mean of the forecast-law chart density against the native cover observable equals a rescaled raw-reference sum
-- statement:
--   **Setting.** Let $m$ be a natural number, $G, X$ finite types, $I : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B$ a family of finite types indexed by `LayerSamplerAxis I n`, $J$ a family of finite types indexed by $\mathrm{Fin}\ m$, $U_j$ a real subspace of $J_j \to \mathbb{R}$, $\mathrm{basis}_j$ a basis indexed by $\mathrm{Fin}\ (n\ j)$ of the orthogonal complement of `euclideanSubspace (U j)`, $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$, and $S$ a `LayerSamplerScale B U basis R σ` (defined by OpenAI, with positive natural number `S.value`). Write "short" for the predicate `allocatedShortAxis U basis S.value` on axes and `selected` for `allocatedShortIntegerSelection U basis S.value` (both defined by OpenAI). Let `law` be a `FiniteProbabilityWeights` (probability weights, defined by OpenAI) on `PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)`; let `density` be a real function on pairs consisting of a real vector indexed by $\Sigma_{x \in X} (\mathrm{Unit} \oplus \mathrm{Empty})$ and a real vector indexed by the non-short axes; let `sample : CoefficientSamplerArrays I n`, $x : G \to$ `IntegerScalarCubeBox Empty S.value`, $\Omega$ a finite type, $E_{\mathrm{out}}$ a family of finite types indexed by $\mathrm{Fin}\ m$, `active` a map from the above integer tuples to `FiniteProbabilityWeights Ω`, and $Y$ a map assigning to each tuple and each $\omega \in \Omega$ an integer vector indexed by `Sigma (AllocatedCongruenceRankOutput X Eout short)`. Let $N$ be a nonzero natural number, $V$ (`volume`) a real number, $\mathrm{base} : X \to \mathbb{Z}$, $\mathrm{physicalN} : X \to \mathbb{N}$, $\tau$ real, and $o_j$ an orthonormal basis of `euclideanSubspace (U j)` indexed by $I\ j$. Let $\mathrm{periodCap}, \mathrm{coverCap}$ be reals and $\mathrm{Lip} \in \mathbb{R}_{\ge 0}$.
--
--   **Hypotheses.** Let $W$ be a `NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip` (defined by OpenAI). Suppose $R_j > 0$ and $\sigma_j > 0$ for all $j$; for every $j$, `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)` holds; $\sigma_{(\mathrm{selected}\ a)_1} \le 1$ for every $a$; and whenever $\mathrm{density}(y) \ne 0$, every component of $y_2$ has absolute value at most $3$. Let $r \in \mathbb{R}_{\ge 0}$ with $r > 0$, $3 \le r$, and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j + 1)}| \le r$ for all $j$. Let $C : \mathrm{Fin}\ m \to \mathbb{R}$ with $C_j \ge 0$, $\lVert \phi_j^{-1}(v) \rVert \le C_j \lVert v \rVert$ for all $j, v$ (where $\phi_j$ = `normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)`), and $C_j\,((|I\ j| + 1)(2 r R_j)) \le 1/4$ for all $j$. Suppose the $\mathbb{Z}$-span of $\mathrm{basis}_j$ is `projectedIntegerLattice (euclideanSubspace (U j))` (hypothesis $hb$); let $bW_j$ be a $\mathbb{Z}$-basis indexed by $E_{\mathrm{out}}\ j$ of the lattice $\Lambda_j$ = `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`, assumed to be a $\mathbb{Z}$-lattice; let $\nu_j$ be a left-invariant probability measure on `euclideanSubspace (U j)` $/\Lambda_j$. Suppose `density` is continuous, and let $\kappa \in \mathbb{C}$.
--
--   **Conclusion.** Let `chart` = `mixedCoveredJetChart U o basis hb bW N` (with one row per layer; a map from `MixedCoveredJetSource` to `EuclideanJetLayers U (fun _ => Unit)`), `region` = `mixedCoveredJetRegion U o basis N Ω₀` with $\Omega_{0,j}$ = `standardLatticeClosedQuarterBox (J j)` $= \{w : |w_i| \le 1/4 \text{ for all } i\}$, and for $u : X \to \mathbb{Z}$ let $\mathrm{src}_u$ = `forecastLawDensityPhysicalChartSource B U basis S law density selected sample x active Y N V base physicalN τ u` (a complex function on the chart source, defined by OpenAI). Let $\mathcal{O}_u$ = `nativeSingleSiteCoverObservable U W physicalN u N` (the observable $y \mapsto$ `W.frozenTorus` evaluated at $u \bmod \texttt{W.modulus}$, at $u_i/\mathrm{physicalN}_i$, and at the covered ambient torus image of $y$ with cover $N / \texttt{W.cover}$). Then
--   $$\kappa\cdot \mathbb{E}_{u \in \texttt{integerBox physicalN}} \int \texttt{restrictedComplexChartDensity chart region 1}\ (\mathrm{src}_u)\ (y)\cdot \mathcal{O}_u(y)\, d\Bigl(\prod_j \nu_j\Bigr)(y)$$
--   equals
--   $$\frac{\kappa\cdot \texttt{coveredJetArrayScale U}}{|\texttt{integerBox physicalN}|}\cdot \sum_{u \in \texttt{integerBox physicalN}} \int \mathrm{src}_u(z)\cdot \mathcal{O}_u(\mathrm{chart}\ z)\, d\,\texttt{mixedCoveredJetRawReference N}(z).$$
--   Here `restrictedComplexChartDensity chart region 1 f` is the function equal to $f(z)$ at points $\mathrm{chart}(z)$ with $z \in \mathrm{region}$ and $0$ elsewhere (via `Function.extend`); `coveredJetArrayScale U` $= \prod_j \mathrm{covol}(\Lambda_j)^{-1}$ (each factor raised to the number of rows, here $1$); `mixedCoveredJetRawReference N` is the product of OpenAI's reference measure on the mixed real/integer coefficient arrays with the uniform measure on the residues modulo $N$; `integerBox physicalN` $= \prod_i [0, \mathrm{physicalN}_i) \cap \mathbb{Z}$ and $\mathbb{E}$ is the uniform average over it.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.forecastLawNativeHaarMean_eq_rawSum_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.forecastLawNativeHaarMean_eq_rawSum` (in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawOriginalNativeHaarJointMean.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B199`, `OAIE3v2B217` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawOriginalNativeHaarJointMean.lean (declaration OAI.Erdos3.VectorPolynomial.forecastLawNativeHaarMean_eq_rawSum)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B199
import Definitions.Def_OAIE3v2B217

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
local notation "selected" => allocatedShortIntegerSelection U basis S.value
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

local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}

theorem forecastLawNativeHaarMean_eq_rawSum_s2
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
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
    (hdensity : Continuous density) (κ : ℂ) :
    let chart := mixedCoveredJetChart (O := single) U o basis hb bW N
    κ * (𝔼 u ∈ integerBox physicalN,
      ∫ y, restrictedComplexChartDensity chart region 1 (chartSource u) y *
        nativeSingleSiteCoverObservable U W physicalN u N y
        ∂Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))) =
      (κ * (coveredJetArrayScale (O := single) U : ℂ) /
        ((integerBox physicalN).card : ℂ)) *
      ∑ u ∈ integerBox physicalN,
        ∫ z, chartSource u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z)
          ∂mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
