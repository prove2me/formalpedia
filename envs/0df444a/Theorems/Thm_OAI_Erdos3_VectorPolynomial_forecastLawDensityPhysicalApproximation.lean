-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastLawDensityPhysicalApproximation
-- name    : OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalApproximation
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T05:49:58.287176+00:00
-- url     : https://prove2.me/theorems/471610e8-e534-496f-ac83-aaa7ea09891b
-- title:
--   A pointwise atom approximation of the density forecast transfers to the physical target
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ and $X$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); short $=$ `allocatedShortAxis U basis S.value`, Spatial $= \Sigma_{x \in X}(\mathrm{Unit}\oplus\mathrm{Empty})$, Active $= \Sigma_{a\ \text{not short}}\,\mathrm{Unit}$, and Principal $=$ `PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)`; finite probability weights law on Principal; a function density $: \mathbb R^{\mathrm{Spatial}} \times \mathbb R^{\mathrm{Active}} \to \mathbb R$; a finite type $A$ and $\mathrm{selected} : A \to \Sigma_j\,\mathrm{Fin}(n_j)$; a sample in `CoefficientSamplerArrays I n` over `LayerSamplerVariables G I n B`; a point $x : G \to$ `IntegerScalarCubeBox Empty S.value`; a finite type $\Omega$ and finite types $E^{\mathrm{out}}_j$, with Out $=$ `Sigma (AllocatedCongruenceRankOutput X Eout short)`; finite probability weights $\mathrm{active}(y)$ on $\Omega$ for each $y \in$ Principal; $Y : \mathrm{Principal} \to \Omega \to \mathrm{Out} \to \mathbb Z$; a natural number $N \ne 0$ and a real number volume; $\mathrm{base} : X \to \mathbb Z$, $\mathrm{physicalN} : X \to \mathbb N$ and a real $\tau$; orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; $\mathbb Z$-span of `basis j` equal to `projectedIntegerLattice (euclideanSubspace (U j))` (hb); and $\mathbb Z$-bases $bW_j$ (indexed by $E^{\mathrm{out}}_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`.
--
--   Let Term be a finite type and Site a type; for each $t \in$ Term let $\chi_t$ be an additive character of $(\mathrm{Out} \to \mathbb Z/N)$ with values in $\mathbb C$ and $e_t$ a family of `ScalarSiteExpansion`s on Site indexed by $A$ (finite families of terms with periods, complex coefficients and factors $\mathbb Z/p \times \mathbb R \to \mathbb C$), with a term choice $k_{t,a}$ for all $t, a$; let $\mathrm{site} \in$ Site, $\mathrm{coefficient} : \mathrm{Term} \to \mathbb C$, $\mathrm{cap} \in \mathbb R_{\ge 0}$ and $\varepsilon \in \mathbb R$. Assume (herror) that for all $z : A \to \mathbb Z$, $\mathrm{out} : \mathrm{Out} \to \mathbb Z/N$ and $y \in \mathbb R^{\mathrm{Spatial}}\times\mathbb R^{\mathrm{Active}}$,
--   $$\Bigl\|\mathrm{density}(y)\cdot\texttt{rationalInactiveForecast law active}\ \mathrm{gp}\ Y\ N\ \mathrm{volume}\ (a, \_ \mapsto z_a)\ \mathrm{out} - \sum_t \mathrm{coefficient}_t\cdot\overline{\chi_t(\mathrm{out})}\cdot\frac{\mathrm{density}(y)}{\mathrm{cap}+1}\cdot\texttt{siteFamilyFactor}\ e_t\ k_t\ \mathrm{site}\ (a \mapsto z_a \bmod p_{k_{t,a}})\ (a \mapsto z_a/\texttt{basisAxisScale (basis j_a) i_a})\Bigr\| \le \varepsilon,$$
--   where $\langle j_a, i_a\rangle = \mathrm{selected}(a)$, gp $=$ `forecastInactiveFixedOutput B U basis S selected (allocatedOriginalSampleInactiveCoefficients B selected sample) x`, and `rationalInactiveForecast law active gp Y N volume z' out` is volume times the law-mean, over the fiber of gp above $z'$, of the rational output density of $(\mathrm{active}(\cdot), Y(\cdot))$ at out. Let $\mathrm{poly}_j$ be `VectorPolynomial X ℝ (J j → ℝ)`s with all coefficients in $U_j$ (hpoly), $u : X \to \mathbb Z$, $w$ with $w_j \in \mathbb R^{I_j}\times\mathbb Z^{\mathrm{Fin}(n_j)}$ and $\mathrm{deck}_j : E^{\mathrm{out}}_j \to \mathbb Z$ such that for every $j$, `normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j) (orthonormalMixedChart (o j) (w j))` plus the lattice vector with $bW_j$-coordinates $\mathrm{deck}_j$ equals `physicalEuclideanSitePoint U poly hpoly u j` (hdeck), and every coordinate of `normalizedLatticePoint (euclideanSubspace (U j)) (basis j) (orthonormalMixedChart (o j) (w j))` has absolute value at most $1/4$ (hquarter). Then
--   $$\Bigl\|\texttt{forecastLawDensityPhysicalTarget B U basis S law density selected sample x active Y N volume base physicalN τ o hb bW poly hpoly u} - \sum_t \mathrm{coefficient}_t\cdot\texttt{forecastDensityNormalizedAtom B U basis S density cap selected}\ (\chi_t)\ (e_t)\ (k_t)\ \mathrm{site}\ \mathrm{base}\ \mathrm{physicalN}\ \tau\ u\ \mathrm{deck}\ w\Bigr\| \le \varepsilon,$$
--   where the target is a restricted chart density (over the covered chart and the quarter-box region) evaluated at `physicalSingleSiteValue U N poly hpoly u`, and the atom is the density at the normalized spatial and active coordinates of $(u, w)$, times $\overline{\chi_t}$ of the congruence output, times the site family factor, divided by $\mathrm{cap}+1$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalApproximation` in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawNativeRawJointMean.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B167`, `OAIErdos3B178` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawNativeRawJointMean.lean#L265

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B167
import Definitions.Def_OAIErdos3B178

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

end Erdos3.VectorPolynomial

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
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
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

theorem forecastLawDensityPhysicalApproximation
    {Term Site : Type*} [Fintype Term]
    (χ : Term → AddChar (Out → ZMod N) ℂ)
    (e : Term → A → ScalarSiteExpansion Site) (k : ∀ t a, (e t a).Term) (site : Site)
    (coefficient : Term → ℂ) (cap : ℝ≥0) {ε : ℝ}
    (herror : ∀ (z : A → ℤ) (out : Out → ZMod N)
        (y : ((Spatial → ℝ) × (Active → ℝ))),
      ‖(density y : ℂ) * (rationalInactiveForecast law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N volume (fun a _ => z a) out : ℂ) -
        ∑ t, coefficient t * ((star (χ t out) * ((density y : ℂ) /
          (((cap : ℝ) + 1 : ℝ) : ℂ))) *
          siteFamilyFactor (e t) (k t) site
            (fun a => (z a : ZMod ((e t a).period (k t a))))
            (fun a => (z a : ℝ) / basisAxisScale (basis (selected a).1) (selected a).2))‖ ≤ ε)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ)
    (hdeck : ∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
      (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
        physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j)
    (hquarter : ∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
      (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) :
    ‖forecastLawDensityPhysicalTarget B U basis S law density selected sample x active Y N volume
        base physicalN τ o hb bW poly hpoly u -
      ∑ t, coefficient t * forecastDensityNormalizedAtom B U basis S density cap selected
        (χ t) (e t) (k t) site base physicalN τ u deck w‖ ≤ ε := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
