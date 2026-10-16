-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastLawDensityPhysicalTarget_ambientHaarComparison
-- name    : OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalTarget_ambientHaarComparison
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T01:53:52.074079+00:00
-- url     : https://prove2.me/theorems/59f82935-d29b-470d-9fe2-d856033e0942
-- title:
--   The twisted physical mean of the forecast target matches a Haar chart integral
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$ and a finite type $X$ (in `Type`) with decidable equality; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` ($= \Sigma_j\,(I_j \oplus \mathrm{Fin}\,n_j)$); finite types $J_j$ (in `Type`), real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$; a layer-sampler scale `S : LayerSamplerScale B U basis R σ` with value $L_S = $ `S.value`; short is the predicate `allocatedShortAxis U basis L_S` on axes and Out $= \Sigma$ `AllocatedCongruenceRankOutput X Eout short`; a finite probability law $\mathrm{law}$ on the principal tuples `PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)`; a real function $\mathrm{density}$ on $(\Sigma_{X}(\mathrm{Unit} \oplus \mathrm{Empty}) \to \mathbb R) \times (\Sigma_{a \text{ non-short}}\mathrm{Unit} \to \mathbb R)$; a type $A$ with a map $\mathrm{selected} : A \to \Sigma_j \mathrm{Fin}\,n_j$; sampler arrays `sample : CoefficientSamplerArrays I n`; a point $x : G \to $ `IntegerScalarCubeBox Empty L_S`; a finite type $\Omega$ and finite types $E^{\mathrm{out}}_j$; for each principal tuple a finite probability law $\mathrm{active}(i)$ on $\Omega$ and a map $Y(i) : \Omega \to \mathrm{Out} \to \mathbb Z$; a natural number $N \neq 0$ and a real $\mathrm{volume}$; $\mathrm{base} : X \to \mathbb Z$, $\mathrm{physicalN} : X \to \mathbb N$ and a real $\tau$; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $hb$: the $\mathbb Z$-span of $\mathrm{basis}_j$ is `projectedIntegerLattice V_j`; $\mathbb Z$-bases $bW_j$ of $\mathbb Z^{J_j} \cap V_j$ indexed by $E^{\mathrm{out}}_j$; additively left-invariant probability measures $\nu_j$ on $V_j/(\mathbb Z^{J_j} \cap V_j)$, with haar $= \prod_j \nu_j$ on `EuclideanJetLayers U (fun _ => Unit)`; and a compact-space instance on `EuclideanJetLayers U (fun _ => Unit)` (included as a hypothesis). Write chart $=$ `mixedCoveredJetChart U o basis hb bW N` and region $=$ `mixedCoveredJetRegion U o basis N (fun j _ => standardLatticeClosedQuarterBox (J j))` (single row per layer), and chartSource $=$ `forecastLawDensityPhysicalChartSource B U basis S law density selected sample x active Y N volume base physicalN τ`.
--
--   Hypotheses: $\mathrm{density}$ is measurable; $T$ is a finite type (in `Type`); reals $p_w, c_w, p_f, c_f$ and $L_w, L_f \in \mathbb R_{\ge 0}$; $W$ : `NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw` and $F_i$ : `NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf` for $i \in T$ (OpenAI's structure bundling a positive modulus and a positive cover bounded by the first two parameters, a residue mask of norm $\le 1$ and a Lipschitz smooth factor of norm $\le 1$); $c : T \to \mathbb C$, $\kappa \in \mathbb C$ and a real $\delta$; $W.\mathrm{cover} \mid N$; for every family of vector polynomials $\mathrm{poly}'_j \in$ `VectorPolynomial X ℝ (J j → ℝ)` with coefficients in $U_j$ and every $u \in \mathbb Z^X$,
--   $$\Bigl\|\kappa\cdot\Theta(\mathrm{poly}', u) - \sum_i c_i\,(F_i).\mathrm{eval}\ \mathrm{physicalN}\ \mathrm{poly}'\ u\Bigr\| \le \delta,$$
--   where $\Theta(\mathrm{poly}', u) = $ `forecastLawDensityPhysicalTarget B U basis S law density selected sample x active Y N volume base physicalN τ o hb bW poly' hm u` (a complex number defined by OpenAI); vector polynomials $\mathrm{poly}_j$ of total degree at most $j+1$ with coefficients in $U_j$; reals $P, E \ge 0$, $R_{\mathrm{rank}}$, $M$ with $|X| \le P$, $|\Sigma_j J_j| \le P$, $L_w\max(1, c_f) + L_f\max(1, c_w) \le e^{P}$, $W.\mathrm{cover}\cdot F_i.\mathrm{cover} \le e^{P}$ and $W.\mathrm{modulus}\cdot F_i.\mathrm{modulus} \le e^{P}$ for all $i$, $\sum_i\|c_i\| \le M$, $\exp((\max(P,E) + A)^A) \le \mathrm{physicalN}_i$ for all $i$ and $\exp((\max(P,E) + A)^A) \le R_{\mathrm{rank}}$, where $A = $ `nativeForecastAmbientExponent m` (a natural number chosen by OpenAI), and `HasLayerSamplingRank (j+1) physicalN R_rank (U j) (poly j)` for every $j$.
--
--   Conclusion:
--   $$\Bigl\|\mathbb E_{u \in \texttt{integerBox physicalN}} W.\mathrm{eval}(\mathrm{physicalN}, \mathrm{poly}, u)\cdot\kappa\,\Theta(\mathrm{poly}, u) - \mathbb E_{u \in \texttt{integerBox physicalN}} \int \kappa\cdot\Delta_u(y)\cdot\Psi_u(y)\,d\,\mathrm{haar}(y)\Bigr\| \le 2\delta + M e^{-E},$$
--   where `integerBox physicalN` $= \prod_i [0, \mathrm{physicalN}_i)$, $\Delta_u = $ `restrictedComplexChartDensity chart region 1 (chartSource u)` and $\Psi_u = $ `nativeSingleSiteCoverObservable U W physicalN u N` (complex-valued functions on `EuclideanJetLayers U (fun _ => Unit)` defined by OpenAI).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalTarget_ambientHaarComparison` in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawPhysicalAmbientHaarComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B167`, `OAIErdos3B1332` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawPhysicalAmbientHaarComparison.lean#L498

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B167
import Definitions.Def_OAIErdos3B1332

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

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
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]


variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]

include hcompact

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} {X : Type} [Fintype G] [Fintype X] [DecidableEq X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
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
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]


variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]

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
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]


variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]

include hcompact

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} {X : Type} [Fintype G] [Fintype X] [DecidableEq X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
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
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))

variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]

include hcompact in
theorem forecastLawDensityPhysicalTarget_ambientHaarComparison
    (hdensity : Measurable density)
    {T : Type} [Fintype T] {pw cw pf cf : ℝ} {Lw Lf : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (F : T → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
    (c : T → ℂ) (κ : ℂ) (δ : ℝ) (hWN : W.cover ∣ N)
    (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j e, coefficients (poly j) e ∈ U j) (u : X → ℤ),
      ‖κ * forecastLawDensityPhysicalTarget B U basis S law density selected sample x
        active Y N volume base physicalN τ o hb bW poly hm u -
          ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (hm : ∀ j a, coefficients (poly j) a ∈ U j)
    {P E Rrank M : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hX : (Fintype.card X : ℝ) ≤ P) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ P)
    (hLip : ((Lw * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hcover : ∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp P)
    (hmod : ∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp P)
    (hmass : ∑ i, ‖c i‖ ≤ M)
    (hlarge : ∀ i, Real.exp ((max P E + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
    (hRrank : Real.exp ((max P E + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
      Rrank (U j) (poly j)) :
    ‖(𝔼 u ∈ integerBox physicalN, W.eval physicalN poly u *
        (κ * forecastLawDensityPhysicalTarget B U basis S law density selected sample x
          active Y N volume base physicalN τ o hb bW poly hm u)) -
      (𝔼 u ∈ integerBox physicalN, ∫ y,
        κ * restrictedComplexChartDensity chart region 1 (chartSource u) y *
          nativeSingleSiteCoverObservable U W physicalN u N y ∂haar)‖ ≤
        2 * δ + M * Real.exp (-E) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
