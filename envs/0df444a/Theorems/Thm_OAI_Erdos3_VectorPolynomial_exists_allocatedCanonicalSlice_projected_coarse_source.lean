-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedCanonicalSlice_projected_coarse_source
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_projected_coarse_source
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T01:46:58.206982+00:00
-- url     : https://prove2.me/theorems/c2c920c8-0b11-46f4-bbe0-3e954442ba85
-- title:
--   Projected profiles at a canonical cover give a recentered coarse source
-- statement:
--   Fix the section data (with universe levels $u_X, u_J, u_G, u_I, u_B$): a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` ($= \Sigma_j\,(I_j \oplus \mathrm{Fin}\,n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$; a layer-sampler scale `S : LayerSamplerScale B U b R σ` with value $L_S = $ `S.value`; the assumption that each $\mathbb Z^{J_j} \cap V_j$ is a full lattice in $V_j$; $hb$: the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice V_j`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $R_j > 0$, $\sigma_j > 0$; $C_{\mathrm{proj}}, V_{\mathrm{proj}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$; a natural number $\mathrm{dim}$; a finite type $X$ with decidable equality, a natural number $\mathrm{modulus} \neq 0$ and $q : X \to \mathbb N$, with $\mathrm{refined} = $ `residueRefinedPeriod modulus q` $= \mathrm{modulus}\cdot\prod_{t} q_t$; natural-valued $H, \mathrm{step}$ and integer-valued $c$ on `PrincipalTupleIndex B (layerSamplerDegree I n)` with $H > 0$ and each progression $\{c_t + \mathrm{step}_t k : 0 \le k < H_t\}$ contained in $[0, \texttt{allocatedPrincipalSides B U b S t})$ ($hsubset$); a label $\ell_0 :$ tuple index $\to \mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z/\mathrm{refined}$ with $hcell$: the tuples with residue label $\ell_0$ have positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH`; law $=$ `containedSupportedProgressionLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c _ hH hsubset refined ℓ₀ hcell` (a finite probability law on the full tuples `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)`); a tuple $y_0$ with $\mathrm{law}(y_0) > 0$, and wholeReference the constant map from labels to $y_0$; a point $x : G \to $ `IntegerScalarCubeBox (Fin dim) L_S`; a natural number $M > 0$, an embedding $\mathrm{selection} : \mathrm{Fin}\,\mathrm{dim} \hookrightarrow G$ and a proof $hx$ of `GoodScalarKernelTuple selection (1/M) M x`, with $hcanonical$: $\mathrm{modulus} = $ `kernelPeriodCandidate (m+1) (goodKernelUniformCandidate selection x hx m)`; $N : X \to \mathbb N$; reals $W \ge 0$, $\tau, \xi$; a real $\mathrm{mesh}$; a finite set $\mathrm{cells}$ of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q`; with $O_j$ the row type of `boundedBooleanJetRows (Fin dim) (j+1)` and $\mathrm{rows}_j$ its inclusion; vector polynomials $\mathrm{poly}_j \in$ `VectorPolynomial X ℝ (J j → ℝ)` of total degree at most $j+1$ with all coefficients in $U_j$ ($hm$), and $\mathrm{point}(d) = $ `physicalCubeRowSample U d rows poly hm`; a signal $f : (X \to \mathbb Z) \to \mathbb C$ with $\|f\| \le 1$, and test $=$ `physicalCubeSiteTest (integerSelfSiteTest dim f)`; $N_t > 0$, $q_t > 0$, $\tau > 0$; reals $C_0, \rho, \delta$ with $\rho > 0$, `allocatedPhysicalRootBudget B U b S 0` $\le W$, $1 \le C_0$, $L_S \le C_0$, $W \le C_0$, $0 < \xi \le 1$, $8(1+W)\,q_t\,\rho \le \xi\tau N_t$, `anisotropicSpatialMeshThreshold selection (tuple index) C₀` $\le \rho$, $8\,$`probabilityProfileLipschitz` $\le \rho$, $\delta \ge 0$, $2\,|\mathrm{Option}(\texttt{LayerSamplerVariables G I n B})|\cdot 2\,$`allocatedPhysicalEntryBudget B U b S 0` $\le \rho$ and $|\text{tuple index}|\cdot 2\,$`allocatedPhysicalEntryBudget B U b S 0` $\le \delta\rho$; $\mathrm{mesh} > 0$; $hmass$: $\sum_z$ `selectedResidueSmoothWeight q cells (narrowTrimmedSpatialWidths W τ ξ N) z` $> 0$; a compact Borel structure on `CoefficientTorus (Fin dim) U` with an additively left-invariant probability measure $\mu$ (which does not appear in the conclusion); additively left-invariant probability measures $\nu_j$ on $V_j/(\mathbb Z^{J_j} \cap V_j)$, with jetHaar $= \prod_j\prod_{O_j}\nu_j$; a compact Borel structure on `CoefficientTorus (LayerSamplerVariables G I n B) U` with an additively left-invariant probability measure $\mu_{\mathrm{coeff}}$; and a Borel structure on `SiteTorus (Finset (Fin dim)) U`. Write spatialError $=$ `allocatedTupleSpatialError |X| selection (tuple index) M modulus C₀ ρ ξ W δ mesh` and boundaryError $= 24\,\texttt{probabilityProfileLipschitz}\cdot|\mathrm{Option}(\texttt{LayerSamplerVariables G I n B}) \times X|/\rho$.
--
--   Let $A_{\mathrm{cover}}$, $A_{\mathrm{sample}}$ be the two natural numbers chosen (in this order) by `exists_allocated_canonical_constructed_projection m dim`, and $A_w$ the natural number chosen by `exists_translated_physical_jet_density_window_mass m dim` (existence theorems of OpenAI, at the indicated universe levels). Hypotheses of the theorem: reals $P_{\mathrm{proj}}, P_k$ with $|G| \le P_{\mathrm{proj}}$, $L_S \le e^{P_{\mathrm{proj}}}$, $M \le e^{P_k}$, $(m+1)P_k \le P_{\mathrm{proj}}$; $\|\texttt{normalizedOrthogonalChart}\ V_j\ b_j\ z\| \le C_{\mathrm{proj}}(j)\|z\|$ and $0 \le$ `mixedDensityCovolumeRatio V_j b_j` $\le V_{\mathrm{proj}}(j)$; $\sigma_j \le 1$; reals $C^{\mathrm{inv}}_j \ge 0$ with $\|(\texttt{normalizedOrthogonalChart}\ V_j\ b_j)^{-1}z\| \le C^{\mathrm{inv}}_j\|z\|$ and $C^{\mathrm{inv}}_j(|I_j|+1)R_j \le 1/4$; $L_f, C_f \in \mathbb R_{\ge 0}$; reals $P_{\mathrm{mass}} \ge 0$ and $R_{\mathrm{rank}}$ with $|X| \le P_{\mathrm{mass}}$, $|\mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \times X| \le P_{\mathrm{mass}}$, $q_i \le e^{P_{\mathrm{mass}}}$, $1/\tau \le e^{P_{\mathrm{mass}}}$, $\exp((P_{\mathrm{mass}} + A_w)^{A_w}) \le N_i$, `HasLayerSamplingRank (j+1) N R_rank (U j) (poly j)` for every $j$, $\exp((P_{\mathrm{mass}} + A_w)^{A_w}) \le R_{\mathrm{rank}}$, $|\texttt{CoefficientAmbientIndex (Fin dim) J}| \le P_{\mathrm{mass}}$, $L_f, C_f \le e^{P_{\mathrm{mass}}}$ and $\sum_j|\texttt{BoundedCoefficientExponent (Fin dim) (j+1)}| \le e^{P_{\mathrm{mass}}}$; a real $C_g \ge 0$ with $\mathrm{cap} \le C_g$ (cap defined below); reals $\mathrm{target}, \kappa$ with $C_g\cdot\mathrm{boundaryError} \le$ `normalizedSpatialShare target`$/2$ and $\mathrm{spatialError}\cdot$`coarseReferenceMassConstant dim X W L_S` $\le$ `normalizedSpatialShare target`$/2$ (`normalizedSpatialShare E` $= e^{-(E+2)}$); reals $p, E \ge 0$ with $|G|, |X|, \mathrm{dim}+1 \le p$, $M \le e^{p}$, $|\texttt{LayerSamplerVariables G I n B}| \le e^{p}$, $W \le |\texttt{LayerSamplerVariables G I n B}|\cdot L_S$, $\mathrm{mesh} \le$ `allocatedEarlyRecenteredMesh X selection M modulus p E`; $1 \le P_{\mathrm{proj}}$, $m \le P_{\mathrm{proj}}$, $|\texttt{LayerSamplerVariables G I n B}| \le P_{\mathrm{proj}}$, $W \le e^{P_{\mathrm{proj}}}$, $R_j^{-1}, \sigma_j^{-1} \le e^{P_{\mathrm{proj}}}$, $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}|, |I_j|, n_j, |J_j| \le P_{\mathrm{proj}}$, `probabilityProfileLipschitz` $\le e^{P_{\mathrm{proj}}}$, $C_{\mathrm{proj}}(j), V_{\mathrm{proj}}(j) \le e^{P_{\mathrm{proj}}}$, $|X|, |\mathrm{Option}(\texttt{LayerSamplerVariables G I n B}) \times X| \le P_{\mathrm{proj}}$, $q_i, \tau^{-1}, \xi^{-1} \le e^{P_{\mathrm{proj}}}$, $\exp((P_{\mathrm{proj}} + A_{\mathrm{sample}})^{A_{\mathrm{sample}}}) \le N_i$ and $\le R_{\mathrm{rank}}$; $\mathrm{cells}$ nonempty; and a nonempty finite set $\mathrm{bases} \subseteq (X \to \mathbb Z)$.
--
--   Put $\mathrm{coverLog} = (P_{\mathrm{proj}} + \mathrm{dim} + 2 + A_{\mathrm{cover}})^{A_{\mathrm{cover}}}$, $\Sigma = $ `CoefficientSlot (LayerSamplerVariables G I n B) m`, $\mathrm{cap} = (\texttt{allocatedAmbientFactorCap B R σ L_S Vproj})^{|\Sigma|}$, $\mathrm{densityLip} = |\Sigma|\cdot$ `allocatedAmbientFactorLip B R σ L_S (fun j => |J j|) Cproj Vproj` $\cdot\,(\texttt{allocatedAmbientFactorCap B R σ L_S Vproj})^{|\Sigma|}$, $\mathrm{sectionLip} = |\mathcal P(\mathrm{Fin}\,\mathrm{dim})|\,e^{\mathrm{coverLog}}$, $\mathrm{reconstructionLip} = \sum_j |\{s \subseteq \mathrm{Fin}\,\mathrm{dim} : |s| \le j+1\}|$, $\mathcal V = $ `narrowTrimmedSpatialWidths W τ ξ N` and $Z = $ `selectedJointDensityMass bases q cells 𝒱 (allocatedJointBaseDensity B U b hb o hR hσ S X poly hm)`. Conclusion: if $\mathrm{coverLog} \le P_{\mathrm{mass}}$, $\mathrm{densityLip}\cdot\mathrm{sectionLip}\cdot\mathrm{reconstructionLip} \le L_f$, $\mathrm{cap} \le C_f$, and $\kappa \le \mathrm{Re}\,\mathbb E_{y \sim \mathrm{law}}$ `allocatedSlicedTupleValue B U b hb o hR hσ S X poly hm N hN hW hτ hξ q cells hmass bases x y f`, then there exist a natural number $\mathrm{cover}$ with $\mathrm{modulus} \mid \mathrm{cover}$ and $0 < \mathrm{cover} \le e^{\mathrm{coverLog}}$, and $g$ assigning to each full tuple $y$ a function $g_y :$ `EuclideanJetLayers U O` $\to \mathbb R$, such that: each $g_y$ is continuous with values in $[0, \mathrm{cap}]$, jetHaar-integrable with $\int g_y\,d\,\mathrm{jetHaar} = 1$; for every $y$ the push-forward of $\mu_{\mathrm{coeff}}$ with density $z \mapsto$ `allocatedCoefficientDensity B U b hb o hR hσ S` (multiplication-by-$\mathrm{cover}$ image of $z$) under `euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S 0 x y) (allocatedPhysicalCubeDirections B U b S x y) rows` equals jetHaar with density $g_y$; for every finite probability law $\lambda$ on full tuples there is an $L_f$-Lipschitz $F : (\texttt{JetAmbientIndex O J} \to \mathbb R/\mathbb Z) \to \mathbb C$ with $\|F\| \le C_f$ and $\mathbb E_{y \sim \lambda}\,g_y(z) = F(\texttt{coveredJetAmbientTorus U 1 z})$ for all $z$; and there is $\mathrm{base} \in \mathrm{bases}$ with $Z \in [1/2, 3/2]$ and
--   $$Z\,\bigl(\kappa - e^{-P_{\mathrm{proj}}} - e^{-\mathrm{target}}\bigr) - e^{-E} \le \mathrm{Re}\,\mathbb E_{y \sim \mathrm{law}}\,\texttt{allocatedRecenteredProfileTerm}(\dots)(y),$$
--   with `allocatedRecenteredProfileTerm B U b S X modulus q wholeReference x hM selection hx N hW (allocatedEarlyRecenteredMesh X selection M modulus p E) base cells (point cover) test (fun y z => g y z)` (a complex-valued function of the full tuple defined by OpenAI).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_projected_coarse_source` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalUniformCoarseSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B199`, `OAIErdos3B1327` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalUniformCoarseSource.lean#L408

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B199
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
local notation "law" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
  hH hsubset refined label₀ hcell
local notation "wholeReference" => (fun _ : labels => y₀)

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
local notation "point" d => physicalCubeRowSample U d rows poly hm
variable (signal : (X → ℤ) → ℂ) (hsignal : ∀ u, ‖signal u‖ ≤ 1)
local notation "test" => physicalCubeSiteTest (integerSelfSiteTest dim signal)


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
local notation "jetHaar" => Measure.pi (fun j => @Measure.pi (O j) _
  (fullBooleanRowSetFintype dim (Fin.val j + 1)) _ (fun _ : O j => ν j))

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)]
variable [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
variable (μcoeff : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μcoeff.IsAddLeftInvariant] [IsProbabilityMeasure μcoeff]

include hp μ hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8
  hcanonical hδ hρshift hρmove hmeshpos hy₀ hsignal in
theorem exists_allocatedCanonicalSlice_projected_coarse_source
    {Pproj Pk : ℝ} (hGproj : (Fintype.card G : ℝ) ≤ Pproj)
    (hLproj : (S.value : ℝ) ≤ Real.exp Pproj)
    (hMkPk : (M : ℝ) ≤ Real.exp Pk) (hperiodP : ((m + 1 : ℕ) : ℝ) * Pk ≤ Pproj)
    (hCactual : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ Cproj j * ‖z‖)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vproj j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (Lf Cf : ℝ≥0)
    {Pmass Rrank : ℝ} (hPmass : 0 ≤ Pmass)
    (hXmass : (Fintype.card X : ℝ) ≤ Pmass)
    (hframe : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pmass)
    (hstrideP : ∀ i, (q i : ℝ) ≤ Real.exp Pmass)
    (hτP : 1 / τ ≤ Real.exp Pmass)
    (hsizeMass : ∀ i, Real.exp ((Pmass + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,0,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,0,max uG uI uB} m dim)) ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRrank : Real.exp ((Pmass + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,0,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,0,max uG uI uB} m dim)) ≤ Rrank)
    (hamb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Pmass)
    (hLf : (Lf : ℝ) ≤ Real.exp Pmass) (hCf : (Cf : ℝ) ≤ Real.exp Pmass)
    (hjet : ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Pmass)
    {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hcapBudget : (allocatedAmbientFactorCap (G := G) B R σ S.value Vproj : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) ≤ Cg)
    {target κ : ℝ}
    (hboundary : Cg * boundaryError ≤ normalizedSpatialShare target / 2)
    (hsite : spatialError * coarseReferenceMassConstant dim X W S.value ≤ normalizedSpatialShare target / 2)
    {p E : ℝ} (hpBudget : 0 ≤ p) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hMP : (M : ℝ) ≤ Real.exp p)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p)
    (hWscale : W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ))
    (hmeshCoarse : mesh ≤ allocatedEarlyRecenteredMesh X selection M modulus p E)
    (hPproj : 1 ≤ Pproj) (hmProj : (m : ℝ) ≤ Pproj)
    (hKproj : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pproj)
    (hWproj : W ≤ Real.exp Pproj)
    (hRproj : ∀ j, (R j)⁻¹ ≤ Real.exp Pproj) (hσproj : ∀ j, (σ j)⁻¹ ≤ Real.exp Pproj)
    (hcountProj : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pproj)
    (hIproj : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pproj) (hnProj : ∀ j, (n j : ℝ) ≤ Pproj)
    (hJproj : ∀ j, (Fintype.card (J j) : ℝ) ≤ Pproj)
    (hProfileProj : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pproj)
    (hCproj : ∀ j, (Cproj j : ℝ) ≤ Real.exp Pproj) (hVproj : ∀ j, (Vproj j : ℝ) ≤ Real.exp Pproj)
    (hXproj : (Fintype.card X : ℝ) ≤ Pproj)
    (hFrameProj : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Pproj)
    (hStrideProj : ∀ i, (q i : ℝ) ≤ Real.exp Pproj)
    (hτProj : τ⁻¹ ≤ Real.exp Pproj) (hξProj : ξ⁻¹ ≤ Real.exp Pproj)
    (hSizeProj : ∀ i, Real.exp ((Pproj + Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim))) ^ Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim))) ≤ (N i : ℝ))
    (hRankProj : Real.exp ((Pproj + Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim))) ^ Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim))) ≤ Rrank)
    (hCells : cells.Nonempty) (bases : Finset (X → ℤ)) (hbases : bases.Nonempty) :
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
    coverLog ≤ Pmass → densityLip * sectionLip * reconstructionLip ≤ Lf → cap ≤ Cf →

    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let Z := selectedJointDensityMass bases q cells V
      (allocatedJointBaseDensity B U b hb o hR hσ S X poly hm)
    κ ≤ ((law).complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hm
      N hN hW hτ hξ q cells hmass bases x y signal)).re →
    ∃ cover : ℕ, modulus ∣ cover ∧ 0 < cover ∧ (cover : ℝ) ≤ Real.exp coverLog ∧
    ∃ g : fullTuple → EuclideanJetLayers U O → ℝ,
      (∀ y, Continuous (g y)) ∧
      (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) jetHaar) ∧
      (∀ y, (∫ z, g y z ∂jetHaar) = 1) ∧
      (∀ y, (realDensityMeasure μcoeff (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) cover z))).map
          (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) rows) = realDensityMeasure jetHaar (g y)) ∧
      (∀ law₁ : FiniteProbabilityWeights fullTuple,
        ∃ F : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
          LipschitzWith Lf F ∧ (∀ z, ‖F z‖ ≤ Cf) ∧
          ∀ z, law₁.complexMean (fun y => (g y z : ℂ)) = F (coveredJetAmbientTorus U 1 z)) ∧
    ∃ base ∈ bases, Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
      Z * (κ - Real.exp (-Pproj) - Real.exp (-target)) - Real.exp (-E) ≤
        ((law).complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
          B U b S X modulus q wholeReference x hM selection hx N hW
          (allocatedEarlyRecenteredMesh X selection M modulus p E) base cells (point cover) test
          (fun y z => (g y z : ℂ)))).re := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
