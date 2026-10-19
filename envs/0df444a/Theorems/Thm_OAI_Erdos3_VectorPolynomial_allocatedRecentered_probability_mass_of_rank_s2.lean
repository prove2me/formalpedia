-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedRecentered_probability_mass_of_rank_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedRecentered_probability_mass_of_rank_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:26:41.233565+00:00
-- url     : https://prove2.me/theorems/f739a509-f8df-4cfb-a648-97074d922381
-- title:
--   Under a sampling-rank hypothesis, the mean recentered profile mass is at most the coarse reference mass constant
-- statement:
--   **Setting.** Let $m, \mathrm{dim}$ be natural numbers, $G$ a finite type with decidable equality, $I : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite types with decidable equality, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n`, $J$ a family of finite types indexed by $\mathrm{Fin}\ m$, $U_j$ a real subspace of $J_j \to \mathbb{R}$, $b_j$ a basis indexed by $\mathrm{Fin}\ (n\ j)$ of the orthogonal complement of `euclideanSubspace (U j)`, $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$, and $S$ a `LayerSamplerScale B U b R σ` (defined by OpenAI, with positive natural number `S.value`). Write $\mathcal{T}$ for `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)` (the "full tuples", defined by OpenAI). Let $X$ be a finite type with decidable equality, $\mathrm{modulus}$ a nonzero natural number, $q : X \to \mathbb{N}$, and `wholeReference` a function from (functions `PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)`) to $\mathcal{T}$, where `residueRefinedPeriod modulus q` $= \mathrm{modulus}\cdot\prod_{t} q(t)$. Let $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value`, $N : X \to \mathbb{N}$, real numbers $W, \tau, \xi$ with $W \ge 0$, $\mathrm{base} : X \to \mathbb{Z}$, and `cells` a finite set of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q` (residue patterns modulo $q$, column by column). Let $O : \mathrm{Fin}\ m \to \mathrm{Type}$ be a family of finite types and $\mathrm{rows}_j : O_j \to \mathrm{Finset}\ (\mathrm{Fin}\ \mathrm{dim})$ injective with $|\mathrm{rows}_j(a)| \le j + 1$ for all $j, a$. Let $\mathrm{cover} \in \mathbb{N}$ and let $\mathrm{poly}_j$ be real vector polynomials on $X$ with values in $J_j \to \mathbb{R}$, of degree at most $j + 1$, with all coefficients in $U_j$ (hypothesis $hm$); write `point` = `physicalCubeRowSample U cover rows poly hm` (a map from integer row data to `EuclideanJetLayers U O`, defined by OpenAI). Assume the coefficient torus `CoefficientTorus U` (for variables $\mathrm{Fin}\ \mathrm{dim}$) is compact with a Borel measurable structure and carries a left-invariant probability measure $\mu$, and for each $j$ let $\nu_j$ be a left-invariant probability measure on the quotient of `euclideanSubspace (U j)` by `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`. Write $\lambda$ for the product measure $\prod_j \prod_{O_j} \nu_j$ on `EuclideanJetLayers U O`.
--
--   **Hypotheses.** Let `law` be a `FiniteProbabilityWeights` on $\mathcal{T}$ (probability weights, defined by OpenAI), and let $g : \mathcal{T} \to$ `EuclideanJetLayers U O` $\to \mathbb{R}$ with $g(y, z) \ge 0$, $g(y, \cdot)$ integrable with respect to $\lambda$, and $\int g(y, z)\, d\lambda(z) = 1$ for every $y$. Let $L_f, C_f \in \mathbb{R}_{\ge 0}$ such that for every $y$ there is $f$ on `JetAmbientIndex O J → UnitAddCircle` which is $L_f$-Lipschitz, has $\lVert f \rVert \le C_f$ everywhere, and satisfies $g(y, z) = f(\texttt{coveredJetAmbientTorus U 1}\ z)$ for all $z$. Suppose $q(t) > 0$ and $N(t) > 0$ for all $t$, $\tau > 0$, $\xi > 0$. Let $P, R_{\mathrm{rank}}, S_{\mathrm{stride}}, \varepsilon_{\mathrm{sample}}, \eta$ be real numbers, and let $A_0$ be the natural number (at least $2$) chosen via `Classical.choose` from OpenAI's existence theorem `exists_translated_physical_jet_density_window_mass m dim` (at the universe levels of this statement). Suppose:
--   - $0 \le P$, $|X| \le P$, $|\mathrm{Option}(\mathrm{Fin}\ \mathrm{dim}) \times X| \le P$;
--   - $0 < \mathrm{cover} \le e^{P}$; $0 \le S_{\mathrm{stride}} \le e^{P}$ and $q(i) \le S_{\mathrm{stride}}$ for all $i$;
--   - $\varepsilon_{\mathrm{sample}} > 0$, $1/\tau \le e^{P}$, $1/\varepsilon_{\mathrm{sample}} \le e^{P}$;
--   - $\exp((P + A_0)^{A_0}) \le N(i)$ for all $i$, `HasLayerSamplingRank (j + 1) N R_rank (U j) (poly j)` for all $j$ (a rank condition defined by OpenAI), and $\exp((P + A_0)^{A_0}) \le R_{\mathrm{rank}}$;
--   - $\eta > 0$, $|\texttt{CoefficientAmbientIndex (Fin dim) J}| \le P$, $L_f \le e^{P}$, $C_f \le e^{P}$, $\sum_j |\texttt{BoundedCoefficientExponent (Fin dim) (j + 1)}| \le e^{P}$, $\eta^{-1} \le e^{P}$, and $2\eta + \varepsilon_{\mathrm{sample}} \le 3$;
--   - $0 < \sum_z$ `selectedResidueSmoothWeight q cells V z` (an unconditional sum over integer points $z$), where $V$ = `narrowTrimmedSpatialWidths W τ ξ N`;
--   - for every $y \in \mathcal{T}$ and all $t, i$: $\sum_k |\texttt{physicalCubeCoefficient}(\mathrm{root}_y, \mathrm{dirs}_y)_{i,k}| \le$ `trimmedSpatialRootScale τ N q t` $= \tau N(t)/8/q(t)$, where $\mathrm{root}_y$ = `allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y` and $\mathrm{dirs}_y$ = `allocatedPhysicalCubeDirections B U b S x y`;
--   - for every $t$: $8\cdot$`probabilityProfileLipschitz` $\le 20\cdot$`trimmedSpatialRootScale τ N q t` (where `probabilityProfileLipschitz` is a fixed constant of OpenAI).
--
--   **Conclusion.** The `law`-mean of the function $y \mapsto$ `allocatedRecenteredProfileMass B U b S X modulus q wholeReference x N base cells point (fun y z => (g y z : ℂ)) y` (with parameters $W, \tau, \xi$; a weighted sum over the residue cells of normalized window sums of $\lVert g(y, \mathrm{point}(\cdot)) \rVert$, defined by OpenAI) is at most `coarseReferenceMassConstant dim X W S.value` $= 4\,(30/\texttt{smoothProbabilityProfile}\ 0)^{|\mathrm{Option}(\mathrm{Fin}\ \mathrm{dim}) \times X|}\,\bigl(((1 + W)/\texttt{S.value})^{\mathrm{dim}}\bigr)^{|X|}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedRecentered_probability_mass_of_rank_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedRecentered_probability_mass_of_rank` (in `lean/OAI/Combinatorics/Progressions/Probability/AllocatedCanonicalSlicedProbabilitySource.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B178`, `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AllocatedCanonicalSlicedProbabilitySource.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedRecentered_probability_mass_of_rank)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B178
import Definitions.Def_OAIE3v2B196

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uX uJ uO uG uI uB

open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type uO} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))
variable (hinj : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)
variable (cover : ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
local notation "point" => physicalCubeRowSample U cover rows poly hm
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "jetHaar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))

include hinj hcard hp μ hW in
omit [DecidableEq G] [NeZero modulus] in
theorem allocatedRecentered_probability_mass_of_rank_s2 [DecidableEq G] [NeZero modulus]
    (law : FiniteProbabilityWeights fullTuple)
    (g : fullTuple → EuclideanJetLayers U O → ℝ)
    (hg0 : ∀ y z, 0 ≤ g y z) (hgi : ∀ y, Integrable (g y) jetHaar)
    (hgmass : ∀ y, (∫ z, g y z ∂jetHaar) = 1)
    (Lf Cf : ℝ≥0)
    (hambient : ∀ y, ∃ f : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
      LipschitzWith Lf f ∧ (∀ z, ‖f z‖ ≤ Cf) ∧
      ∀ z, (g y z : ℂ) = f (coveredJetAmbientTorus U 1 z))
    (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ) (hξ : 0 < ξ)
    {P Rrank Sstride εsample η : ℝ}
    (hP : 0 ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (hframe : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (hcover : 0 < cover) (hcoverP : (cover : ℝ) ≤ Real.exp P)
    (hSstride : 0 ≤ Sstride) (hSstrideP : Sstride ≤ Real.exp P)
    (hstride : ∀ i, (q i : ℝ) ≤ Sstride)
    (hε : 0 < εsample) (hτP : 1 / τ ≤ Real.exp P) (hεP : 1 / εsample ≤ Real.exp P)
    (hsize : ∀ i, Real.exp ((P + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRrank : Real.exp ((P + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ≤ Rrank)
    (hη : 0 < η) (hamb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ P)
    (hLf : (Lf : ℝ) ≤ Real.exp P) (hCf : (Cf : ℝ) ≤ Real.exp P)
    (hjet : ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hηP : η⁻¹ ≤ Real.exp P) (hsmall : 2 * η + εsample ≤ 3)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (hrowsize : ∀ y : fullTuple, ∀ t i,
      (∑ k, |(physicalCubeCoefficient (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) i k : ℝ)|) ≤ trimmedSpatialRootScale τ N q t)
    (hscale : ∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * trimmedSpatialRootScale τ N q t) :
    law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point (fun y z => (g y z : ℂ))) ≤
      coarseReferenceMassConstant dim X W S.value := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
