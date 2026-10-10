-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCanonicalSlice_model_source_of_length
-- name    : OAI.Erdos3.VectorPolynomial.allocatedCanonicalSlice_model_source_of_length
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T10:16:25.110615+00:00
-- url     : https://prove2.me/theorems/7498774f-6c16-499d-9307-3d943e35035b
-- title:
--   Long enough canonical slices transfer a recentered profile bound to the model source
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ (hR) and $\sigma_j > 0$ (hσ); a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); $\mathrm{dim} \in \mathbb N$ and finite families $\mathrm{rowSets}_j$ of finsets of $\mathrm{Fin}\,\mathrm{dim}$ (selectedRows$_j$ the subtype, rows$_j$ the inclusion); a point $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value`; $M_k \in \mathbb N$ with $M_k > 0$ (hMk) and an embedding $\mathrm{selection} : \mathrm{Fin}\,\mathrm{dim} \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/Mk) Mk x` (hgood); a finite type $X_0$ and $\mathrm{stride}_0 : X_0 \to \mathbb N$; a real $P \ge 0$ (hP) with $M_k \le e^P$, $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$ and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^P$ for all $j$ (hMkP, hRP, hRi, hσi, hcount); finite types $Q_j$; $\mathbb Z$-span of `basis j` equal to `projectedIntegerLattice (euclideanSubspace (U j))` (hb); orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; $\mathbb Z$-bases $bW_j$ (indexed by $Q_j$) of $\Lambda_j =$ `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`, each a $\mathbb Z$-lattice; a natural number $d \ne 0$; $H_0, \mathrm{step}_0 : \mathrm{FullInput} \to \mathbb N$ and $c_0 : \mathrm{FullInput} \to \mathbb Z$ (FullInput $=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`) with $H_0 > 0$ and each `integerProgressionSupport (c₀ t) (step₀ t) (H₀ t)` contained in $[0,$ `allocatedPrincipalSides B U basis S t`$)$; $\mathrm{modulus} =$ `canonicalSlicedModulus selection stride₀ m x` (with $M = M_k$; hcanonical); a residue label $r_0 : \mathrm{FullInput} \to \mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z/\mathrm{modulus}$ whose cell has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H₀ hH₀` (hcell); left-invariant probability measures $\nu_j$ on the tori `euclideanSubspace (U j)` $/\Lambda_j$; a left-invariant probability measure $\mu$ on the compact Borel group `CoefficientTorus U` over `LayerSamplerVariables G I n B`, and one $\mu_{\mathrm{rows}}$ on `CoefficientTorus U` over $\mathrm{Fin}\,\mathrm{dim}$; and a finite type $X$ with decidable equality. Let grid be the predicate `allocatedGridAxis U basis S.value`; Tuple the principal tuple index over the non-grid axes, with $H, \mathrm{step}, c$ the restrictions of $H_0, \mathrm{step}_0, c_0$ to Tuple and $L$ the side lengths `allocatedPrincipalSides` there; wholeLaw $=$ `containedSupportedProgressionLaw … H₀ step₀ c₀ … hH₀ hsubset₀ modulus r₀ hcell` and gridLaw the corresponding `containedSupportedProgressionAxisLaw … grid`; jetHaar the product of the $\nu_j$ over rows; density $=$ `allocatedCoefficientDensity B U basis hb o hR hσ S`; and cover $=$ `quotientIntegerCover (coefficientIntegerLattice U) d`.
--
--   Let $D, \mathrm{target}, P_k, P_\rho, F, Q_{\mathrm{stride}}$ be reals with `AllocatedComparisonDimensions B (Fin dim) selectedRows D` (that is, $D \ge 0$ bounds $m$, $|G|$, $\mathrm{dim}$, the numbers of axes, tuples, block parameters, outputs, rows, coefficient exponents, and `probabilityProfileLipschitz`), $P_k, P_\rho, \mathrm{target}, F, Q_{\mathrm{stride}} \ge 0$, $M_k \le e^{P_k}$, $0 < \mathrm{stride}_0(i) \le e^{Q_{\mathrm{stride}}}$ for all $i$, and $\exp(\texttt{allocatedAffineLengthLog m D P Prho Pk target F}\ ((m+1)P_k + |X_0|Q_{\mathrm{stride}})) \le S.\mathrm{value}$. Let $g$ assign to each tuple $y$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U basis S)` a measurable, nonnegative, jetHaar-integrable function $g_y$ on `EuclideanJetLayers U selectedRows` such that the image of the measure with density $\mathrm{density}\circ\mathrm{cover}$ with respect to $\mu$ under `euclideanCoefficientJetMap U root_y dirs_y rows` equals the measure with density $g_y$ with respect to jetHaar, where root$_y$, dirs$_y$ are `allocatedPhysicalCubeRoot B U basis S 0 x y` and `allocatedPhysicalCubeDirections B U basis S x y`. Let $\delta, \eta$ be reals, $\rho$ assign to each predicate on axes an element of $\mathbb R_{\ge 0}$, and $t \le 1$ real, with `AllocatedAffineCoveredComparison B rows δ η ρ t` (OpenAI's uniform comparison statement for affine covered profiles); assume $0 < \rho(\mathrm{grid}) \le 1$, $\sigma_j \le t$, $\mathrm{step}_j > 0$ on Tuple, $\delta > 0$ with $\delta^{-1} \le e^F$, $\delta L_j \le |\texttt{integerProgressionSupport (c j) (step j) (H j)}|$ on Tuple, $\mathrm{dim} \le m+1$, every $a \in \mathrm{rowSets}_j$ has $|a| \le j+1$; let $y_0$ have positive wholeLaw weight; let $T : \mathrm{Fin}\,m \to \mathbb R$ with `partitionedIdealRadius (Fin dim) m` $+1 \le T_j$ and $|\texttt{BoundedCoefficientExponent …(j+1)}|\cdot 2^{\mathrm{dim}}(\mathrm{dim}+1)^{j+1} \le T_j$; let $C : \mathrm{Fin}\,m \to \mathbb R$ with $C_j \ge 0$, $\|(\texttt{normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)})^{-1}v\| \le C_j\|v\|$ and $C_j(|I_j|+1)T_jR_j \le 1/4$; and assume $\rho(\mathrm{grid})^{-1} \le e^{P_\rho}$ and $0 \le \eta \le \exp(-(\mathrm{target} + 1 + D\cdot m2^{m+1}P_k + 4))$.
--
--   Put center $=$ `principalProgressionSliceCenter … L c`, width $=$ `principalProgressionSliceWidth … L H step`, ideal $=$ `diagonalImageDensity (o ↦ R_{layer(o)}) (activeAveragedSlicedProfileIdeal … grid rows (ρ grid) center width)`, and $\mathrm{profile}(y) = \mathrm{gridLaw.mean}\bigl(u \mapsto \texttt{allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows hb o bW d}\ (\texttt{principalAxisJoin grid u}\ (\texttt{principalAxisRestrict (¬ grid) y₀}))\ \mathrm{modulus}\ \mathrm{ideal}\ y\bigr)$. Then the following holds for every natural number $\mathrm{spatialModulus} \ne 0$ and $\mathrm{stride}, N : X \to \mathbb N$, with refined $=$ `residueRefinedPeriod spatialModulus stride` and labels the maps $\mathrm{FullInput} \to \mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z/\mathrm{refined}$; every map wholeReference from labels to the tuples above and every label $r$ such that every $y$ of nonzero wholeLaw weight has `principalResidueLabel refined y` $= r$ and `principalResidueLabel refined (wholeReference r)` $= r$; all reals $W \ge 0, \tau, \xi_n, \mathrm{mesh}$, $\mathrm{base} : X \to \mathbb Z$, finsets cells of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride`, `VectorPolynomial X ℝ (J j → ℝ)`s $\mathrm{poly}_j$ of degree at most $j+1$ with all coefficients in $U_j$, and $\mathrm{test}$ from integer cubes $X \to (\mathrm{Unit}\oplus\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z$ to $\mathbb C$, with point $=$ `physicalCubeRowSample U d rows poly hmem`; every model $:$ `EuclideanJetLayers U selectedRows` $\to \mathbb C$; and all reals $\kappa$, loss, $\varepsilon_{\mathrm{trunc}}$, $P_{\mathrm{sample}}$, $R_{\mathrm{rank}}$, $S_{\mathrm{stride}}$, $\varepsilon_{\mathrm{sample}}$, $\eta_{\mathrm{sample}}$, $\delta_{\mathrm{sur}}$:
--
--   if $\mathrm{stride} > 0$, $N > 0$, $\tau > 0$, $\mathrm{mesh} > 0$; `allocatedPhysicalRootBudget B U basis S (fun _ => 0)` $\le W$; $\mathrm{spatialModulus}\cdot\mathbb Z^{\mathrm{Unit}\oplus\mathrm{Fin}\,\mathrm{dim}}$ is contained in `pivotFullImage` of the selected spatial pivot and free columns of $(g \mapsto x_g(\mathrm{none}))$ and `scalarCubeDifferenceMatrix x` at selection; $\|\mathrm{test}\| \le 1$; $\kappa \le \mathrm{Re}$ of the wholeLaw complex mean of `allocatedRecenteredProfileTerm B U basis S X spatialModulus stride wholeReference x hMk selection hgood N hW mesh base cells point test (y z ↦ g y z)` (with $\tau, \xi_n$); $0 \le \varepsilon_{\mathrm{trunc}}$ and $\|\mathrm{profile}(z) - \mathrm{model}(z)\| \le \varepsilon_{\mathrm{trunc}}$; $P_{\mathrm{sample}} \ge 0$ bounds $|X|$, $(\mathrm{dim}+1)|X|$ and $|\texttt{CoefficientAmbientIndex (Fin dim) J}|$, while $d$, $S_{\mathrm{stride}}$ (with $0 \le S_{\mathrm{stride}}$), $1/\tau$, $1/\varepsilon_{\mathrm{sample}}$ (with $\varepsilon_{\mathrm{sample}} > 0$), $\eta_{\mathrm{sample}}^{-1}$ (with $\eta_{\mathrm{sample}} > 0$) and $\sum_j|\texttt{BoundedCoefficientExponent (Fin dim) (j+1)}|$ are at most $e^{P_{\mathrm{sample}}}$; $\mathrm{stride}(i) \le S_{\mathrm{stride}}$; with $A$ the natural number chosen by `exists_translated_physical_jet_l1_perturbation m dim`, $\exp((P_{\mathrm{sample}} + A)^A) \le N(i)$ for all $i$ and $\le R_{\mathrm{rank}}$, and `HasLayerSamplingRank (j+1) N Rrank (U j) (poly j)` for all $j$; there are functions actual, surrogate on the torus `JetAmbientIndex selectedRows J` $\to \mathbb R/\mathbb Z$, Lipschitz with constants $L_a, L_s$ and bounded in norm by $C_a, C_s$, all four at most $e^{P_{\mathrm{sample}}}$, with $\mathrm{wholeLaw.mean}(v \mapsto g_v(y)) = \mathrm{actual}(\texttt{coveredJetAmbientTorus U 1 y})$ and $\|\mathrm{profile}(y) - \mathrm{surrogate}(\texttt{coveredJetAmbientTorus U 1 y})\| \le \delta_{\mathrm{sur}}$ for all $y$; and, with root, dirs at wholeReference $r$, $H_{sp} =$ `trimmedSpatialRootScale τ N stride`, $V =$ `narrowTrimmedSpatialWidths W τ ξn N`, $C_{sp} = (\mathrm{spatialModulus}^{\mathrm{dim}+1}\cdot$`anisotropicSpatialDensityCap selection (1/Mk)`$)^{|X|}$ and $\mathrm{volumeFactor} = (30/\texttt{smoothProbabilityProfile 0})^{(\mathrm{dim}+1)|X|}((1+W)/S.\mathrm{value})^{\mathrm{dim}|X|}$: $V > 0$, $\sum_z$ `selectedResidueSmoothWeight stride cells V z` $> 0$, $\sum_k|\texttt{physicalCubeCoefficient root dirs i k}| \le H_{sp}(t)$, $8\cdot$`probabilityProfileLipschitz` $\le 20H_{sp}(t)$, $1 \le H_{sp}(t)$, and $C_{sp}\bigl(\mathrm{volumeFactor}(e^{-\mathrm{target}} + 2\delta_{\mathrm{sur}} + 2\eta_{\mathrm{sample}} + \varepsilon_{\mathrm{sample}}) + 9^{(\mathrm{dim}+1)|X|}((1+W)/S.\mathrm{value})^{\mathrm{dim}|X|}\varepsilon_{\mathrm{trunc}}\bigr) \le \mathrm{loss}$ — then
--   $$\kappa - \mathrm{loss} \le \mathrm{Re}\sum_{(c', v) \in \mathrm{cells}\times\texttt{spatialWindow}\ H_{sp}\ 4}\texttt{selectedResidueCellWeight stride cells V c'}\cdot\texttt{allocatedRecenteredResidueWeight B U basis S X spatialModulus stride wholeReference x hMk selection hgood N hW mesh base cells test r c' v}\cdot\mathrm{model}\bigl(\mathrm{point}(\texttt{allocatedWholeResidueReconstruction B U basis S X spatialModulus stride wholeReference x base r c' v})\bigr)$$
--   (the residue weight taken with $\tau$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedCanonicalSlice_model_source_of_length` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalSliceConstructedModelSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B162`, `OAIErdos3B200` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalSliceConstructedModelSource.lean#L105

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B162
import Definitions.Def_OAIErdos3B200

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ uX
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {dim : ℕ}
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable [∀ j, Nonempty (rowSets j)]
local notation "selectedRows" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (selection : Fin dim ↪ G)
variable (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
variable {X₀ : Type*} [Fintype X₀] (stride₀ : X₀ → ℕ)
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ)
variable (hcanonical : modulus = canonicalSlicedModulus (M := Mk) selection stride₀ m x)
variable (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := (Fin dim)) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j => Measure.pi (fun _ : rowSets j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin dim) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

omit [∀ j, Nonempty (rowSets j)] in
include hcanonical μrows hR hσ hMk hgood hP hMkP hRP hRi hσi hcount in
theorem allocatedCanonicalSlice_model_source_of_length
    {D target Pk Prho F Qstride : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin dim) selectedRows D)
    (hPk : 0 ≤ Pk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target) (hF : 0 ≤ F) (hQstride : 0 ≤ Qstride)
    (hstride₀ : ∀ i, 0 < stride₀ i) (hstrideBound : ∀ i, (stride₀ i : ℝ) ≤ Real.exp Qstride)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card X₀ * Qstride)) ≤ S.value)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U basis S) →
  EuclideanJetLayers U selectedRows → ℝ)
    (hgm : ∀ y, Measurable (g y)) (hg0 : ∀ y z, 0 ≤ g y z)
    (hgi : ∀ y, Integrable (g y) jetHaar)
    (hglaw : ∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
  (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) = realDensityMeasure jetHaar (g y))
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j)
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hq : Fintype.card (Fin dim) ≤ m + 1)
    (hrowDegree : ∀ j (a : rowSets j), a.val.card ≤ j.val + 1)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U basis S))
    (hy₀ : 0 < (wholeLaw).weight y₀)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius (Fin dim) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin dim) * ((Fintype.card (Fin dim) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4))) :
    let center := principalProgressionSliceCenter (α := (Fin dim)) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := (Fin dim)) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, selectedRows a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option (Fin dim))
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let profile := fun y => ((gridLaw).mean (fun u =>
      allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows
        hb o bW d (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) modulus ideal y) : ℂ)
    ∀ (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : X → ℕ),
    let refined := residueRefinedPeriod spatialModulus stride
    let labels := PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined
    ∀ (wholeReference : labels → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
        (allocatedPrincipalSides B U basis S)) (r : labels),
    (∀ y, (wholeLaw).weight y ≠ 0 → principalResidueLabel refined y = r) →
    principalResidueLabel refined (wholeReference r) = r →
    ∀ {W τ ξn mesh : ℝ} (hW : 0 ≤ W) (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ),
    let point := physicalCubeRowSample U d rows poly hmem
    ∀ (model : EuclideanJetLayers U selectedRows → ℂ)
      {κ loss εtrunc Psample Rrank Sstride εsample ηsample δsur : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → 0 < τ → 0 < mesh →
    allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W →
    integerScalarLattice (Unit ⊕ Fin dim) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection) →
    (∀ v, ‖test v‖ ≤ 1) →
    κ ≤ ((wholeLaw).complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξn)
      B U basis S X spatialModulus stride wholeReference x hMk selection hgood N hW mesh base cells point test
      (fun y z => (g y z : ℂ)))).re →
    0 ≤ εtrunc → (∀ z, ‖profile z - model z‖ ≤ εtrunc) →
    0 ≤ Psample → (Fintype.card X : ℝ) ≤ Psample →
    (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Psample →
    (d : ℝ) ≤ Real.exp Psample →
    0 ≤ Sstride → Sstride ≤ Real.exp Psample → 0 < εsample →
    1 / τ ≤ Real.exp Psample → 1 / εsample ≤ Real.exp Psample →
    (∀ i, (stride i : ℝ) ≤ Sstride) →
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{uX,uJ,0} m dim)
    (∀ i, Real.exp ((Psample + A) ^ A) ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    ∀ (actual surrogate : (JetAmbientIndex selectedRows J → UnitAddCircle) → ℂ)
      (La Ls Ca Cs : ℝ≥0),
    LipschitzWith La actual → LipschitzWith Ls surrogate →
    (∀ z, ‖actual z‖ ≤ Ca) → (∀ z, ‖surrogate z‖ ≤ Cs) →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Psample →
    (La : ℝ) ≤ Real.exp Psample → (Ls : ℝ) ≤ Real.exp Psample →
    (Ca : ℝ) ≤ Real.exp Psample → (Cs : ℝ) ≤ Real.exp Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    (∀ y, ((wholeLaw).mean (fun v => g v y) : ℂ) = actual (coveredJetAmbientTorus U 1 y)) →
    (∀ y, ‖profile y - surrogate (coveredJetAmbientTorus U 1 y)‖ ≤ δsur) →
    let root := allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (wholeReference r)
    let dirs := allocatedPhysicalCubeDirections B U basis S x (wholeReference r)
    let Hsp := trimmedSpatialRootScale τ N stride
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    let Csp := ((spatialModulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (Mk : ℝ))) ^ Fintype.card X
    let volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    (∀ z, 0 < V z) → (0 < ∑' z, selectedResidueSmoothWeight stride cells V z) →
    (∀ t i, (∑ k, |(physicalCubeCoefficient root dirs i k : ℝ)|) ≤ Hsp t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * Hsp t) →
    (∀ t, 1 ≤ Hsp t) →
    Csp * (volumeFactor * (Real.exp (-target) + 2 * δsur + (2 * ηsample + εsample)) +
      ((9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
        (((1 + W) / S.value) ^ dim) ^ Fintype.card X) * εtrunc) ≤ loss →
    κ - loss ≤
      (∑ t : cells × spatialWindow (α := Fin dim) Hsp 4, (selectedResidueCellWeight stride cells V t.1 : ℂ) *
        allocatedRecenteredResidueWeight (τ := τ) B U basis S X spatialModulus stride wholeReference x hMk selection hgood
          N hW mesh base cells test r t.1 t.2.val *
        model (point (allocatedWholeResidueReconstruction B U basis S X spatialModulus stride wholeReference x base r
          t.1.val t.2.val))).re := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
