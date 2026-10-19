-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastLawDensityPhysicalDeckSource_cutoff_s2
-- name    : OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalDeckSource_cutoff_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:46:56.648207+00:00
-- url     : https://prove2.me/theorems/79736f51-5edb-4173-9e6d-717eaa1db4e9
-- title:
--   Where the forecast-law density physical deck source is nonzero, the normalized coordinate cutoff of the site values equals one
-- statement:
--   All named objects below are defined by OpenAI. Let $m$ be a natural number, $G$ and $X$ finite types, and for $j < m$ let $I_j$, $J_j$, $E^{\mathrm{out}}_j$ be finite types and $n_j$ natural numbers; let $B_a$ be finite types indexed by `LayerSamplerAxis I n`. For each $j$ let $U_j$ be a real subspace of $\mathbb{R}^{J_j}$ and `basis j` a basis, indexed by $\{0,\dots,n_j-1\}$, of the orthogonal complement of the Euclidean copy of $U_j$. Let $R_j, \sigma_j$ be reals and $S$ a `LayerSamplerScale B U basis R σ` (scale value `S.value`). Write short for `allocatedShortAxis U basis S.value` and $\mathcal{P}$ for `PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)`. Let:
--   - `law` be a finite probability distribution on $\mathcal{P}$;
--   - `density` a real function on pairs (a vector indexed by $X$ (one coordinate per $x \in X$), a vector indexed by the non-short axes);
--   - $A$ a type and `selected` a map from $A$ to pairs $(j, i)$ with $i < n_j$;
--   - `sample` a `CoefficientSamplerArrays` value (over `LayerSamplerVariables G I n B`), and $x : G \to$ `IntegerScalarCubeBox Empty S.value`;
--   - $\Omega$ a finite type, `active` a map from $\mathcal{P}$ to finite probability distributions on $\Omega$, and $Y$ a map assigning to $y \in \mathcal{P}$ and $\omega \in \Omega$ an integer vector indexed by the dependent pairs of `AllocatedCongruenceRankOutput X Eout short`;
--   - $N$ a nonzero natural number, `volume` and $\tau$ reals, `base : X → ℤ` and `physicalN : X → ℕ`.
--
--   Write deckSource for `forecastLawDensityPhysicalDeckSource B U basis S law density selected sample x active Y N volume base physicalN τ`; evaluated at $u : X \to \mathbb{Z}$, $w$ (for each $j$ a pair of a real vector indexed by $I_j$ and an integer vector indexed by $\{0,\dots,n_j-1\}$) and `deck` (integer vectors indexed by $E^{\mathrm{out}}_j$), it is the complex number
--   `density` $\bigl((x \mapsto (u_x - \mathrm{base}_x)/(\tau\,\mathrm{physicalN}_x/8)),\ \texttt{forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue U basis w)}\bigr)$ times OpenAI's `rationalInactiveForecast` built from `law`, `active`, the inactive fixed output of `sample` and $x$ along `selected`, $Y$, $N$, `volume`, the integer entries of $w$ at the selected pairs, and the congruence output of $u$, $w$, `deck` reduced mod $N$.
--
--   Assume:
--   - $R_j > 0$ and $\sigma_j > 0$ for all $j$;
--   - for every $j$, `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)` holds;
--   - $\sigma_{j} \le 1$ whenever $(j, i)$ = `selected a` for some $a$;
--   - every short axis $a$ equals $(j, \mathrm{inr}\ i)$ for some value $(j, i)$ of `selected`;
--   - whenever `density y` $\ne 0$, every coordinate of the second component of $y$ has absolute value at most $3$;
--   - $r$ is a nonnegative real with $r > 0$, $3 \le r$, and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| \le r$ for all $j < m$;
--   - $u$, $w$, `deck` as above satisfy `deckSource u w deck` $\ne 0$.
--
--   Then
--   $$\texttt{normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr}\bigl(\texttt{allocatedFullMixedSiteValue U basis w}\bigr) = 1,$$
--   where `normalizedCoordinateCutoff D r hr` is a fixed smooth compactly supported function on $\mathbb{R}^D$ with values in $[0,1]$, chosen by OpenAI so that it equals $1$ whenever all coordinates have absolute value at most $r$ and vanishes unless all coordinates have absolute value at most $2r$; and `allocatedFullMixedSiteValue U basis w` sends the axis $(j, \mathrm{inl}\ i)$ to $(w_j)_1(i)/R_j$ and $(j, \mathrm{inr}\ i)$ to $(w_j)_2(i)\,/\,\texttt{basisAxisScale}(\mathrm{basis}_j, i)\,/\,R_j$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalDeckSource_cutoff_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalDeckSource_cutoff` (in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawNativeRawJointMean.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B199` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawNativeRawJointMean.lean (declaration OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalDeckSource_cutoff)

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
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

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

local notation "deckSource" => forecastLawDensityPhysicalDeckSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem forecastLawDensityPhysicalDeckSource_cutoff_s2
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
    (u : X → ℤ) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ)
    (hnonzero : deckSource u w deck ≠ 0) :
    normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr
      (allocatedFullMixedSiteValue (R := R) U basis w) = 1 := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
