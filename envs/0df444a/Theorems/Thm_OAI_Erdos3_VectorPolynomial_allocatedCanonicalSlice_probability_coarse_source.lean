-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCanonicalSlice_probability_coarse_source
-- name    : OAI.Erdos3.VectorPolynomial.allocatedCanonicalSlice_probability_coarse_source
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T11:38:40.613726+00:00
-- url     : https://prove2.me/theorems/fe022c45-a9d8-4343-b244-6bc0c6ef1472
-- title:
--   A coarse projected probability mean bounds the early recentered profile mean
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); $\mathrm{dim} \in \mathbb N$, with fullTuple $=$ `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)`; a finite type $X$ with decidable equality, a natural number $\mathrm{modulus} \ne 0$ and $q : X \to \mathbb N$, with refined $=$ `residueRefinedPeriod modulus q` $= \mathrm{modulus}\cdot\prod_t q(t)$ and labels the maps $\mathrm{FullInput} \to \mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z/\mathrm{refined}$ (FullInput $=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`); $H, \mathrm{step} : \mathrm{FullInput} \to \mathbb N$ and $c : \mathrm{FullInput} \to \mathbb Z$ with $H > 0$ (hH) and each `integerProgressionSupport (c t) (step t) (H t)` contained in $[0,$ `allocatedPrincipalSides B U b S t`$)$ (hsubset); a label $\lambda_0$ whose cell has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH` (hcell); law $=$ `containedSupportedProgressionLaw … H step c … hH hsubset refined λ₀ hcell` and a tuple $y_0$ of positive law weight (hy₀), with wholeReference the constant map on labels with value $y_0$; a point $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value`; $M \in \mathbb N$ with $M > 0$ (hM) and an embedding $\mathrm{selection} : \mathrm{Fin}\,\mathrm{dim} \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/M) M x` (hx); $\mathrm{modulus} =$ `kernelPeriodCandidate (m+1) (goodKernelUniformCandidate selection x hx m)` (hcanonical); $N : X \to \mathbb N$ with $N > 0$ (hN), $q > 0$ (hq); reals $W \ge 0$ (hW), $\tau > 0$ (hτ), $0 < \xi \le 1$ (hξ, hξ1); a real $\mathrm{mesh} > 0$ (hmeshpos); $\mathrm{base} : X \to \mathbb Z$; a finset cells of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q`; finite types $O_j$ and injective maps $\mathrm{rows}_j : O_j \to \mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim})$ (hinj) with $|\mathrm{rows}_j(a)| \le j+1$ (hcard); a natural number cover; `VectorPolynomial X ℝ (J j → ℝ)`s $\mathrm{poly}_j$ of degree at most $j+1$ (`DegreeLE 1 (j+1)`, hp) with all coefficients in $U_j$ (hm), and point $=$ `physicalCubeRowSample U cover rows poly hm`; test from integer cubes $X \to (\mathrm{Unit}\oplus\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z$ to $\mathbb C$ with $\|\mathrm{test}\| \le 1$ (htest); reals $C_0, \rho, \delta$ with $\rho > 0$ (hρ), $1 \le C_0$, $S.\mathrm{value} \le C_0$, $W \le C_0$ (hC₀, hLC, hWC), $\delta \ge 0$ (hδ); `allocatedPhysicalRootBudget B U b S (fun _ => 0)` $\le W$ (hbudget); $8(1+W)q(t)\rho \le \xi\tau N(t)$ for all $t$ (hsize); `anisotropicSpatialMeshThreshold selection FullInput C₀` $\le \rho$ (hmesh); $8\cdot$`probabilityProfileLipschitz` $\le \rho$ (hρ8); $2|\mathrm{Option}(\texttt{LayerSamplerVariables G I n B})|\cdot 2\cdot$`allocatedPhysicalEntryBudget B U b S (fun _ => 0)` $\le \rho$ (hρshift); $|\mathrm{FullInput}|\cdot 2\cdot$`allocatedPhysicalEntryBudget B U b S (fun _ => 0)` $\le \delta\rho$ (hρmove); $\sum_z$ `selectedResidueSmoothWeight q cells V z` $> 0$ (hmass), where $V =$ `narrowTrimmedSpatialWidths W τ ξ N`; a left-invariant probability measure $\mu$ on the compact Borel group `CoefficientTorus U` over $\mathrm{Fin}\,\mathrm{dim}$; and left-invariant probability measures $\nu_j$ on the tori `euclideanSubspace (U j)` modulo `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`, with jetHaar their product over rows. Write spatialError $=$ `allocatedTupleSpatialError |X| selection FullInput M modulus C₀ ρ ξ W δ mesh` and boundaryError $= 24\cdot$`probabilityProfileLipschitz`$\cdot(\mathrm{dim}+1)|X|/\rho$.
--
--   Let $g$ assign to each $y \in$ fullTuple a nonnegative, jetHaar-integrable function $g_y$ on `EuclideanJetLayers U O` with $\int g_y\,d\mathrm{jetHaar} = 1$; let $L_f, C_f \in \mathbb R_{\ge 0}$ such that for every $y$ there is an $L_f$-Lipschitz $f$ on the torus `JetAmbientIndex O J` $\to \mathbb R/\mathbb Z$ with $\|f\| \le C_f$ and $g_y(z) = f(\texttt{coveredJetAmbientTorus U 1 z})$ for all $z$. Let $P_{\mathrm{mass}}, R_{\mathrm{rank}}$ be reals with $P_{\mathrm{mass}} \ge 0$ bounding $|X|$, $(\mathrm{dim}+1)|X|$ and $|\texttt{CoefficientAmbientIndex (Fin dim) J}|$; $0 < \mathrm{cover} \le e^{P_{\mathrm{mass}}}$; $q(i)$, $1/\tau$, $L_f$, $C_f$ and $\sum_j|\texttt{BoundedCoefficientExponent (Fin dim) (j+1)}|$ at most $e^{P_{\mathrm{mass}}}$; and, with $A$ the natural number chosen by `exists_translated_physical_jet_density_window_mass m dim`, $\exp((P_{\mathrm{mass}} + A)^A) \le N(i)$ for all $i$ and $\le R_{\mathrm{rank}}$, and `HasLayerSamplingRank (j+1) N Rrank (U j) (poly j)` for all $j$. Let $C_g \ge 0$ with $|g_y(\mathrm{point}(v))| \le C_g$ whenever $y$ has nonzero law weight, $Z \ge 1/2$, and reals target, $\kappa$ with $C_g\cdot\mathrm{boundaryError} \le$ `normalizedSpatialShare target` $/2$ and $\mathrm{spatialError}\cdot$`coarseReferenceMassConstant dim X W S.value` $\le$ `normalizedSpatialShare target` $/2$. Let $p, E \ge 0$ with $|G|, |X|, \mathrm{dim}+1 \le p$, $M \le e^p$, $|\texttt{LayerSamplerVariables G I n B}| \le e^p$, $W \le |\texttt{LayerSamplerVariables G I n B}|\cdot S.\mathrm{value}$, and $\mathrm{mesh} \le$ `allocatedEarlyRecenteredMesh X selection M modulus p E`.
--
--   Define $\mathrm{projected}(y) = \sum_z \mathbb P(z)\cdot\mathrm{test}(w_{y,z})\cdot g_y(\mathrm{point}(w_{y,z}))$, where $\mathbb P$ is the PMF `selectedResidueSmoothPMF q cells V` and $w_{y,z} =$ `physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S 0 x y) (allocatedPhysicalCubeDirections B U b S x y) base z`. If $\kappa \le \mathrm{Re}(\mathrm{law.complexMean}(\mathrm{projected})/Z)$, then
--   $$Z\,(\kappa - e^{-\mathrm{target}}) - e^{-E} \le \mathrm{Re}\ \mathrm{law.complexMean}\bigl(\texttt{allocatedRecenteredProfileTerm B U b S X modulus q wholeReference x hM selection hx N hW}\ \mathrm{mesh}'\ \texttt{base cells point test}\ (y, z \mapsto g_y(z))\bigr),$$
--   with $\mathrm{mesh}' =$ `allocatedEarlyRecenteredMesh X selection M modulus p E` and the profile term taken with $\tau, \xi$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedCanonicalSlice_probability_coarse_source` in `lean/OAI/Combinatorics/Progressions/Probability/AllocatedCanonicalSlicedProbabilitySource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B199` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AllocatedCanonicalSlicedProbabilitySource.lean#L375

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B199

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
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)


variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uX uJ uO uG uI uB
open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S

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
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)


variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
  pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
    (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (htest : ∀ v, ‖test v‖ ≤ 1)


variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uX uJ uO uG uI uB
open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) (q : X → ℕ)
local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) →
  ZMod (residueRefinedPeriod modulus q))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel (residueRefinedPeriod modulus q) y = label₀)))
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hy₀ : 0 < (containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
  hH hsubset (residueRefinedPeriod modulus q) label₀ hcell).weight y₀)
local notation "law" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
  hH hsubset refined label₀ hcell
local notation "wholeReference" => (fun _ : labels => y₀)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (hcanonical : modulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
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


variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (htest : ∀ v, ‖test v‖ ≤ 1)

local notation "spatialError" => allocatedTupleSpatialError (Fintype.card X) selection
  (PrincipalTupleIndex B (layerSamplerDegree I n)) M modulus C₀ ρ ξ W δ mesh
local notation "boundaryError" => (24 * (probabilityProfileLipschitz : ℝ) *
  Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ)

variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "jetHaar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))

include hinj hcard hp μ hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8
  hcanonical hδ hρshift hρmove hmeshpos htest hy₀ in
theorem allocatedCanonicalSlice_probability_coarse_source
    (g : fullTuple → EuclideanJetLayers U O → ℝ)
    (hg0 : ∀ y z, 0 ≤ g y z) (hgi : ∀ y, Integrable (g y) jetHaar)
    (hgmass : ∀ y, (∫ z, g y z ∂jetHaar) = 1)
    (Lf Cf : ℝ≥0)
    (hambient : ∀ y, ∃ f : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
      LipschitzWith Lf f ∧ (∀ z, ‖f z‖ ≤ Cf) ∧
      ∀ z, (g y z : ℂ) = f (coveredJetAmbientTorus U 1 z))
    {Pmass Rrank : ℝ} (hPmass : 0 ≤ Pmass)
    (hXmass : (Fintype.card X : ℝ) ≤ Pmass)
    (hframe : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pmass)
    (hcover : 0 < cover) (hcoverP : (cover : ℝ) ≤ Real.exp Pmass)
    (hstrideP : ∀ i, (q i : ℝ) ≤ Real.exp Pmass)
    (hτP : 1 / τ ≤ Real.exp Pmass)
    (hsizeMass : ∀ i, Real.exp ((Pmass + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRrank : Real.exp ((Pmass + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ≤ Rrank)
    (hamb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Pmass)
    (hLf : (Lf : ℝ) ≤ Real.exp Pmass) (hCf : (Cf : ℝ) ≤ Real.exp Pmass)
    (hjet : ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Pmass)
    {Cg Z : ℝ} (hCg : 0 ≤ Cg)
    (hcap : ∀ y, (law).weight y ≠ 0 → ∀ v, ‖(g y (point v) : ℂ)‖ ≤ Cg) (hZ : 1 / 2 ≤ Z) {target κ : ℝ}
    (hboundary : Cg * boundaryError ≤ normalizedSpatialShare target / 2)
    (hsite : spatialError * coarseReferenceMassConstant dim X W S.value ≤ normalizedSpatialShare target / 2)
    {p E : ℝ} (hpBudget : 0 ≤ p) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hMP : (M : ℝ) ≤ Real.exp p)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p)
    (hWscale : W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ))
    (hmeshCoarse : mesh ≤ allocatedEarlyRecenteredMesh X selection M modulus p E) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let projected := fun y => ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
          (g y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)) : ℂ))
    κ ≤ ((law).complexMean projected / (Z : ℂ)).re →
    Z * (κ - Real.exp (-target)) - Real.exp (-E) ≤
      ((law).complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW
          (allocatedEarlyRecenteredMesh X selection M modulus p E) base cells point test (fun y z => (g y z : ℂ)))).re := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
