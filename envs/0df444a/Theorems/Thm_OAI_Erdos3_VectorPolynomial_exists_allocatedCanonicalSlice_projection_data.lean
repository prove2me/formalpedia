-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedCanonicalSlice_projection_data
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_projection_data
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:46:51.453697+00:00
-- url     : https://prove2.me/theorems/67decc46-1a6b-4499-b25c-581dd2490cf0
-- title:
--   Projection data at a cover divisible by the canonical kernel period
-- statement:
--   Fix the section data (with universe levels $u_X, u_J, u_G, u_I, u_B$): a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` ($= \Sigma_j\,(I_j \oplus \mathrm{Fin}\,n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$; a layer-sampler scale `S : LayerSamplerScale B U b R σ` with value $L_S = $ `S.value`; the assumption that each $\mathbb Z^{J_j} \cap V_j$ is a full lattice in $V_j$; $hb$: the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice V_j`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $R_j > 0$, $\sigma_j > 0$; $C_{\mathrm{proj}}, V_{\mathrm{proj}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$; a natural number $\mathrm{dim}$, with $O_j$ the row type of `boundedBooleanJetRows (Fin dim) (j+1)` (subsets of size at most $j+1$) and $\mathrm{rows}_j$ its inclusion into $\mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim})$; a point $x : G \to $ `IntegerScalarCubeBox (Fin dim) L_S`; a natural number $M$, an embedding $\mathrm{selection} : \mathrm{Fin}\,\mathrm{dim} \hookrightarrow G$ and a proof $hx$ of `GoodScalarKernelTuple selection (1/M) M x`; a compact Borel structure on `CoefficientTorus (Fin dim) U` with an additively left-invariant probability measure $\mu$; additively left-invariant probability measures $\nu_j$ on $V_j/(\mathbb Z^{J_j} \cap V_j)$, with jetHaar $= \prod_j \prod_{O_j} \nu_j$; a compact Borel structure on `CoefficientTorus (LayerSamplerVariables G I n B) U` with an additively left-invariant probability measure $\mu_{\mathrm{coeff}}$; and a Borel structure on `SiteTorus (Finset (Fin dim)) U`. The measure $\mu$ is a hypothesis of the theorem but does not appear in its conclusion.
--
--   Let $P_{\mathrm{proj}}, P_k$ be reals with $P_{\mathrm{proj}} \ge 0$, $|G| \le P_{\mathrm{proj}}$, $L_S \le e^{P_{\mathrm{proj}}}$, $M \le e^{P_k}$ and $(m+1)P_k \le P_{\mathrm{proj}}$; assume $\|\texttt{normalizedOrthogonalChart}\ V_j\ b_j\ z\| \le C_{\mathrm{proj}}(j)\|z\|$ and $0 \le$ `mixedDensityCovolumeRatio V_j b_j` $\le V_{\mathrm{proj}}(j)$ for every $j$; $\sigma_j \le 1$; reals $C^{\mathrm{inv}}_j \ge 0$ with $\|(\texttt{normalizedOrthogonalChart}\ V_j\ b_j)^{-1}z\| \le C^{\mathrm{inv}}_j\|z\|$ and $C^{\mathrm{inv}}_j(|I_j|+1)R_j \le 1/4$; and $L_f, C_f \in \mathbb R_{\ge 0}$.
--
--   Let $A_{\mathrm{cover}}$ and $A_{\mathrm{sample}}$ be the two natural numbers chosen (in this order) by the existence theorem `exists_allocated_canonical_constructed_projection m dim` (at the indicated universe levels); put $\mathrm{coverLog} = (P_{\mathrm{proj}} + \mathrm{dim} + 2 + A_{\mathrm{cover}})^{A_{\mathrm{cover}}}$, $\Sigma = $ `CoefficientSlot (LayerSamplerVariables G I n B) m` $= \Sigma_{j}\,$`BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)`, $\mathrm{cap} = (\texttt{allocatedAmbientFactorCap B R σ L_S Vproj})^{|\Sigma|}$, $\mathrm{densityLip} = |\Sigma|\cdot$ `allocatedAmbientFactorLip B R σ L_S (fun j => |J j|) Cproj Vproj` $\cdot\,(\texttt{allocatedAmbientFactorCap B R σ L_S Vproj})^{|\Sigma|}$ (explicit nonnegative reals defined by OpenAI), $\mathrm{sectionLip} = |\mathcal P(\mathrm{Fin}\,\mathrm{dim})|\cdot e^{\mathrm{coverLog}}$ and $\mathrm{reconstructionLip} = \sum_j |\{s \subseteq \mathrm{Fin}\,\mathrm{dim} : |s| \le j+1\}|$.
--
--   Conclusion: if $\mathrm{densityLip}\cdot\mathrm{sectionLip}\cdot\mathrm{reconstructionLip} \le L_f$ and $\mathrm{cap} \le C_f$, then there exists a natural number $\mathrm{cover}$, divisible by `kernelPeriodCandidate (m+1) (goodKernelUniformCandidate selection x hx m)`, with $0 < \mathrm{cover} \le e^{\mathrm{coverLog}}$, and there exists $g$ assigning to each full tuple $y$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)` a function $g_y : $ `EuclideanJetLayers U O` $\to \mathbb R$, such that: each $g_y$ is continuous with values in $[0, \mathrm{cap}]$, jetHaar-integrable, with $\int g_y\,d\,\mathrm{jetHaar} = 1$; for every $y$, the push-forward of $\mu_{\mathrm{coeff}}$ with density $z \mapsto$ `allocatedCoefficientDensity B U b hb o hR hσ S` (the multiplication-by-$\mathrm{cover}$ image of $z$ in the coefficient torus) under the additive map `euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S 0 x y) (allocatedPhysicalCubeDirections B U b S x y) rows` equals jetHaar with density $g_y$; for every $y$ there is an $L_f$-Lipschitz $f : (\texttt{JetAmbientIndex O J} \to \mathbb R/\mathbb Z) \to \mathbb C$ with $\|f\| \le C_f$ and $g_y(z) = f(\texttt{coveredJetAmbientTorus U 1 z})$ for all $z$; for every finite probability law $\lambda$ on full tuples there is an $L_f$-Lipschitz $F$ on the same ambient torus with $\|F\| \le C_f$ and $\mathbb E_{y \sim \lambda}\, g_y(z) = F(\texttt{coveredJetAmbientTorus U 1 z})$ for all $z$; and `AllocatedSlicedSourceProjection B U b S x hb o hR hσ Cproj Vproj cover g A_sample Pproj` holds (OpenAI's predicate on $g$, quantifying over admissible parameters bounded in terms of $P_{\mathrm{proj}}$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_projection_data` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalUniformCoarseSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1327` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalUniformCoarseSource.lean#L334

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1327

namespace OAI

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
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (Cproj Vproj : Fin m → ℝ≥0)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S

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

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (hcanonical : modulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
local notation "O" => (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (Fin.val j + 1) : Type))
local notation "rows" => (fun j => (Subtype.val : O j → Finset (Fin dim)))
variable (cover : ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
variable (signal : (X → ℤ) → ℂ) (hsignal : ∀ u, ‖signal u‖ ≤ 1)


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
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (Cproj Vproj : Fin m → ℝ≥0)
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

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (hcanonical : modulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
local notation "O" => (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (Fin.val j + 1) : Type))
local notation "rows" => (fun j => (Subtype.val : O j → Finset (Fin dim)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
variable (signal : (X → ℤ) → ℂ) (hsignal : ∀ u, ‖signal u‖ ≤ 1)


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


variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "jetHaar" => Measure.pi (fun j => @Measure.pi (O j) _
  (fullBooleanRowSetFintype dim (Fin.val j + 1)) _ (fun _ : O j => ν j))

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)]
variable [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
variable (μcoeff : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μcoeff.IsAddLeftInvariant] [IsProbabilityMeasure μcoeff]

include μ in
theorem exists_allocatedCanonicalSlice_projection_data
    {Pproj Pk : ℝ} (hPproj0 : 0 ≤ Pproj) (hGproj : (Fintype.card G : ℝ) ≤ Pproj)
    (hLproj : (S.value : ℝ) ≤ Real.exp Pproj)
    (hMkPk : (M : ℝ) ≤ Real.exp Pk) (hperiodP : ((m + 1 : ℕ) : ℝ) * Pk ≤ Pproj)
    (hCactual : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ Cproj j * ‖z‖)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vproj j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (Lf Cf : ℝ≥0)
    :
    let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim)
    let coverLog := (Pproj + (dim + 2 : ℕ) + Acover) ^ Acover
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value Vproj : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) Cproj Vproj *
      allocatedAmbientFactorCap (G := G) B R σ S.value Vproj ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin dim)) : ℝ≥0) * Real.toNNReal (Real.exp coverLog)
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin dim) (j.val + 1)) : ℝ≥0)
    densityLip * sectionLip * reconstructionLip ≤ Lf → cap ≤ Cf →

    ∃ cover : ℕ, kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m) ∣ cover ∧ 0 < cover ∧ (cover : ℝ) ≤ Real.exp coverLog ∧
    ∃ g : fullTuple → EuclideanJetLayers U O → ℝ,
      (∀ y, Continuous (g y)) ∧
      (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) jetHaar) ∧
      (∀ y, (∫ z, g y z ∂jetHaar) = 1) ∧
      (∀ y, (realDensityMeasure μcoeff (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) cover z))).map
          (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) rows) = realDensityMeasure jetHaar (g y)) ∧
      (∀ y, ∃ f : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
        LipschitzWith Lf f ∧ (∀ z, ‖f z‖ ≤ Cf) ∧
        ∀ z, (g y z : ℂ) = f (coveredJetAmbientTorus U 1 z)) ∧
      (∀ law₁ : FiniteProbabilityWeights fullTuple,
        ∃ F : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
          LipschitzWith Lf F ∧ (∀ z, ‖F z‖ ≤ Cf) ∧
          ∀ z, law₁.complexMean (fun y => (g y z : ℂ)) = F (coveredJetAmbientTorus U 1 z)) ∧
      AllocatedSlicedSourceProjection.{uX} B U b S x hb o hR hσ Cproj Vproj cover g
        (Classical.choose (Classical.choose_spec
          (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim))) Pproj := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
