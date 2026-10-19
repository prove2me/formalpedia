-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastLawDensityPhysicalTarget_nativeHaarExpansion_s2
-- name    : OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalTarget_nativeHaarExpansion_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:07:48.29267+00:00
-- url     : https://prove2.me/theorems/505fa24c-7b0a-4af6-9921-ad43bef4011e
-- title:
--   A twist expansion of the forecast-law physical target transfers to the native Haar expansion of the chart density
-- statement:
--   Let $m$ be a natural number and $G, X$ finite types. For each $j < m$ let $I_j$ and $J_j$ be finite types, $n_j$ a natural number, $U_j$ a real subspace of $\mathbb{R}^{J_j}$ and $\mathrm{basis}_j$ a real basis, indexed by $\{0, \dots, n_j - 1\}$, of the orthogonal complement of the Euclidean subspace $V_j$ given by $U_j$; for each layer sampler axis $a$ (OpenAI's `LayerSamplerAxis I n`) let $B_a$ be a finite type. Let $R, \sigma : \{0,\dots,m-1\} \to \mathbb{R}$ and $S$ a layer sampler scale (OpenAI's `LayerSamplerScale B U basis R σ`, main field a positive natural number `S.value`). Fix the following data (all types and functions as in OpenAI's definitions): finite probability weights `law` on the principal integer tuples (with $\alpha$ empty and sides `allocatedPrincipalSides B U basis S`); a real function `density` on pairs (a real vector indexed by $X$, a real vector indexed by the non-short axes); a map `selected` from a type $A$ to pairs $(j, i)$ with $i < n_j$; a sample (OpenAI's `CoefficientSamplerArrays`); $x : G \to$ `IntegerScalarCubeBox Empty S.value`; a finite type $\Omega$ and finite types $E^{\mathrm{out}}_j$; for each principal tuple, probability weights `active` on $\Omega$ and an integer-valued map $Y$ on $\Omega \times$ (OpenAI's congruence rank outputs); a nonzero natural number $N$; reals `volume` and $\tau$; $\mathrm{base} : X \to \mathbb{Z}$ and $\mathrm{physicalN} : X \to \mathbb{N}$; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; the hypothesis $hb$ that each $\mathbb{Z}$-span of $\mathrm{basis}_j$ equals OpenAI's projected integer lattice of $V_j$; $\mathbb{Z}$-bases $bW_j$, indexed by $E^{\mathrm{out}}_j$, of the lattice section $\Lambda_j = \mathbb{Z}^{J_j} \cap V_j$; and left-invariant probability measures $\nu_j$ on the tori $V_j/\Lambda_j$. Assume that the product of these tori (OpenAI's `EuclideanJetLayers U (fun _ => Unit)`, one copy for each $j$) is compact, and write $\mathrm{haar}$ for the product of the $\nu_j$ on it.
--
--   Let `chart` = `mixedCoveredJetChart U o basis hb bW N` and `region` = `mixedCoveredJetRegion U o basis N (closed quarter boxes)` be OpenAI's covered jet chart (from OpenAI's mixed covered jet source space to the product of tori) and its source region, and for $u : X \to \mathbb{Z}$ let `chartSource u` be OpenAI's complex function `forecastLawDensityPhysicalChartSource … u` on the source space, built from all the data above. OpenAI's `restrictedComplexChartDensity chart region 1 f` is the function on the tori whose value at $\mathrm{chart}(s)$ is $f(s)$ for $s$ in the region, and $0$ off the image of the region (via `Function.extend`). For a family $\mathrm{poly}_j$ of vector polynomials (elements of OpenAI's `VectorPolynomial X ℝ (J j → ℝ)`, i.e. polynomials in variables indexed by $X$ with coefficients in $\mathbb{R}^{J_j}$) with all coefficients in $U_j$, `forecastLawDensityPhysicalTarget … poly hm u` (OpenAI) is that restricted chart density of `chartSource u` evaluated at the physical single-site value of $\mathrm{poly}$ at $u$.
--
--   A `NormalizedPolynomialTwist X (Σ j, J j) pc cc L` (OpenAI) consists of a modulus $\mu > 0$ at most $pc$, a cover $\gamma > 0$ at most $cc$, a mask $(\mathbb{Z}/\mu)^{X} \to \mathbb{C}$ bounded by $1$, and an $L$-Lipschitz function $\mathrm{smooth}$ on $\mathbb{R}^{X} \times (\mathbb{R}/\mathbb{Z})^{\sqcup_j J_j}$ bounded by $1$; its frozen torus function at residue $r$, center $c$ and torus point $y$ is $\mathrm{mask}(r)\,\mathrm{smooth}(c, y)$. Twists have a product (modulus and cover multiply) and an evaluation `eval physicalN poly u` (OpenAI).
--
--   Now assume `density` is measurable. Let $T$ be a finite type, $p_w, c_w, p_f, c_f$ reals and $L_w, L_f \ge 0$; let $W$ be a twist with caps $p_w, c_w$ and Lipschitz constant $L_w$, and $F_i$ ($i \in T$) twists with caps $p_f, c_f$ and constant $L_f$; let $c : T \to \mathbb{C}$, $\kappa \in \mathbb{C}$, $\delta \in \mathbb{R}$, and assume the cover of $W$ divides $N$. Assume that for every family $\mathrm{poly}$ as above and every $u : X \to \mathbb{Z}$,
--   $$\Bigl|\kappa\cdot\texttt{forecastLawDensityPhysicalTarget}(\ldots, \mathrm{poly}, u) - \sum_{i \in T} c_i\, F_i.\mathrm{eval}(\mathrm{physicalN}, \mathrm{poly}, u)\Bigr| \le \delta.$$
--   Then for every $u : X \to \mathbb{Z}$,
--   $$\Bigl|\int \kappa\cdot \texttt{restrictedComplexChartDensity}\ \mathrm{chart}\ \mathrm{region}\ 1\ (\mathrm{chartSource}\ u)(y)\cdot \texttt{nativeSingleSiteCoverObservable}\ U\ W\ \mathrm{physicalN}\ u\ N\ y \, d\mathrm{haar}(y) - \sum_{i \in T} c_i\, (W \cdot F_i).\texttt{frozenSingleSiteHaarReference}\ U\ \nu\ (u \bmod \mu_i)\ \bigl(u/\mathrm{physicalN}\bigr)\Bigr| \le \delta,$$
--   where $\mu_i$ is the modulus of the product twist $W \cdot F_i$, $u/\mathrm{physicalN}$ is the vector $(u_\xi/\mathrm{physicalN}_\xi)_\xi$, `nativeSingleSiteCoverObservable U W physicalN u N y` (OpenAI) is the frozen torus function of $W$ at residue $u \bmod (\text{modulus of } W)$, center $u/\mathrm{physicalN}$ and the covered jet ambient torus point of $y$ at level $N/\gamma_W$ (natural-number division by the cover $\gamma_W$ of $W$), and `frozenSingleSiteHaarReference U ν r c` (OpenAI) is the $\mathrm{haar}$-integral of the frozen torus function at $r$, $c$ and the covered jet ambient torus point of $y$ at level $1$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalTarget_nativeHaarExpansion_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalTarget_nativeHaarExpansion` (in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawPhysicalAmbientHaarComparison.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B216`, `OAIE3v2B217`, `OAIE3v2B301` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastLawPhysicalAmbientHaarComparison.lean (declaration OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalTarget_nativeHaarExpansion)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216
import Definitions.Def_OAIE3v2B217
import Definitions.Def_OAIE3v2B301

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

include hcompact

theorem forecastLawDensityPhysicalTarget_nativeHaarExpansion_s2
    (hdensity : Measurable density)
    {T : Type*} [Fintype T] {pw cw pf cf : ℝ} {Lw Lf : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (F : T → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
    (c : T → ℂ) (κ : ℂ) (δ : ℝ) (hWN : W.cover ∣ N)
    (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j e, coefficients (poly j) e ∈ U j) (u : X → ℤ),
      ‖κ * forecastLawDensityPhysicalTarget B U basis S law density selected sample x
        active Y N volume base physicalN τ o hb bW poly hm u -
          ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ)
    (u : X → ℤ) :
    ‖(∫ y, κ * restrictedComplexChartDensity chart region 1 (chartSource u) y *
        nativeSingleSiteCoverObservable U W physicalN u N y ∂haar) -
      ∑ i, c i * (W.product (F i)).frozenSingleSiteHaarReference U ν
        (fun j => (u j : ZMod (W.product (F i)).modulus))
        (fun j => (u j : ℝ) / physicalN j)‖ ≤ δ := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
