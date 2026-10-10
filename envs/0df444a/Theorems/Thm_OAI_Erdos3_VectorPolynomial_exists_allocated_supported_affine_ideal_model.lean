-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_supported_affine_ideal_model
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_ideal_model
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T09:02:38.902743+00:00
-- url     : https://prove2.me/theorems/beea9dcc-69d8-4331-8026-ccbcba07dbff
-- title:
--   Chart expansion of the row-sliced ideal times a full-grid site expansion
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` ($= \Sigma_j\, (I_j \oplus \mathrm{Fin}\,n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$; a layer-sampler scale `S : LayerSamplerScale B U b R σ` with value $L_S = $ `S.value`; a finite type $\alpha$ (in a universe $u_\alpha$) with decidable equality and finite families $\mathrm{rowSets}_j$ of subsets of $\alpha$, with row types $\mathrm{rowTypes}_j = \{t : t \in \mathrm{rowSets}_j\}$ and $\mathrm{rows}_j$ the inclusion into $\mathrm{Finset}\,\alpha$; finite types $E_j$; a point $x : G \to $ `IntegerScalarCubeBox α L_S`; a tuple $y_0$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)`; natural numbers $q$, $d \neq 0$, $\mathrm{period} \neq 0$; $r \in \mathbb R_{\ge 0}$ with $r > 0$; $hb$: the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice V_j` for every $j$; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $\mathbb Z$-bases $bW_j$ of $\mathbb Z^{J_j} \cap V_j$ indexed by $E_j$; $hperiod$: $\mathrm{period}\cdot\mathbb Z^{\mathrm{rowTypes}_j}$ is contained in the range of `scalarKernelIntegerJet x (j+1) (rows j)` for every $j$; a real $M \ge 1$ with $hm$: $0 \le$ `allocatedIntegerKernelMask B U b S x rows j q (residue j) z` $\le M$ for all $j, z$, where `residue j` $=$ `integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x (y₀|grid) rows j (y₀|¬grid)) q` and grid is the predicate `allocatedGridAxis U b L_S` on axes; $R_j > 0$ and $\sigma_j > 0$ for all $j$; reals $C_j \ge 0$ with $\|(\texttt{normalizedOrthogonalChart}\ V_j\ b_j)^{-1} v\| \le C_j\|v\|$ and $(|\mathrm{rowSets}_j|+1)\,|\mathcal P(\alpha)|\,C_j(|I_j|+1)\,2rR_j \le 1/4$; $\rho \in \mathbb R_{\ge 0}$; real functions $\mathrm{center}, \mathrm{width}$ on `PrincipalAxisParameter (fun a => ¬ grid a)`; natural-valued $H, \mathrm{step}$ and integer-valued $c$ on `PrincipalTupleIndex B (layerSamplerDegree I n)` with $H > 0$ and each progression `integerProgressionSupport (c t) (step t) (H t)` $= \{c_t + \mathrm{step}_t k : 0 \le k < H_t\}$ contained in $[0, \texttt{allocatedPrincipalSides B U b S t})$; a label $\ell : $ tuple index $\to \mathrm{Option}\,\alpha \to \mathbb Z/q$ with $hcell$: the tuples whose residues mod $q$ (`principalResidueLabel q`) equal $\ell$ have positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH`; $hu_0$: the restriction of $y_0$ to the grid axes has nonzero weight under gridLaw $=$ `containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c _ hH hsubset q ℓ hcell grid` (a finite probability law on grid-axis tuples); $hmodulus$: $q\cdot\mathbb Z^{\mathrm{rowTypes}_j}$ is contained in the range of `scalarKernelIntegerJet x (j+1) (rows j)` for every $j$; and $hy_0$: each $y_0(t)$ satisfies `IntegerScalarCube (allocatedPrincipalSides B U b S t)`.
--
--   Let $e$ assign to each grid axis $a$ a `ScalarSiteExpansion (Finset α)` (a structure bundling a finite term type, periods, complex coefficients and factor functions), and let $\varepsilon_{\mathrm{grid}}$ be a real such that $\bigl\|\texttt{allocatedFullGridNaturalVolume B U b S rowSets}\cdot \mathrm{gridDensity}(z) - \texttt{allocatedFullGridSiteApproximation B U b S rowSets e}(z)\bigr\| \le \varepsilon_{\mathrm{grid}}$ for every $z$ in `AllocatedFrozenJetRows B U b S rowTypes`, where $\mathrm{gridDensity} = $ `allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q ℓ hcell x`. Let $N_t, V, C_c, H_s$ be real functions on the grid axes and $L_g \in \mathbb R_{\ge 0}$ with `(e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a)` for every $a$ (at most $N_t(a)$ terms, positive periods $\le V(a)$, coefficient $\ell^1$-norm $\le C_c(a)$, factors bounded by $1$, $L_g$-Lipschitz and vanishing for $|x| \ge H_s(a)$). Assume $0 < \rho \le 1$, $|\mathrm{center}_i| + |\mathrm{width}_i| \le 1$ for all $i$, and reals $\varepsilon > 0$, $p \ge 0$ with $2\rho_s \le e^{p}$, $\varepsilon^{-1} \le e^{p}$, $\rho^{-1} \le e^{p}$, where $\rho_s = $ `allocatedRowSlicedSiteRadius rowSets`. Put $\Lambda = |\texttt{LayerSamplerAxis I n}|\cdot\texttt{normalizedSiteCutoffBound}/(2\rho_s)$, $Q = $ `idealSiteLogBudget (card (Σ a, rowTypes a.1)) (card α) p`, $A = \exp(|\mathcal P(\alpha)|\,|\texttt{LayerSamplerAxis I n}|\,(4Q+8) + Q)$, $\mathrm{maskCap} = M^{|\texttt{LayerSamplerAxis I n}|}\cdot$ `coefficientDeckPeriodCap rowTypes E period`, $N = $ `allocatedProductIdealNormalizer B U b S rowSets`, $\mathcal L = (\prod_j \mathrm{Fin}\,n_j \to \mathbb Z/\mathrm{period}) \times (\prod_j E_j \to \mathbb Z/\mathrm{period})$, ideal $=$ `allocatedRowSlicedIdeal B U b S rowSets ρ center width` and prefactor $=$ `allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ ideal`.
--
--   Then there exists a natural number $k$ with $k \le e^{4Q+8}$ and $|K| \le \exp(|\mathcal P(\alpha)|\,|\texttt{LayerSamplerAxis I n}|\,(4Q+8))$ for $K = (\mathcal P(\alpha) \times \texttt{LayerSamplerAxis I n} \to \mathrm{Fin}\,k)$, and there exist $a : K \to \mathbb C$ and $f : K \to \mathcal P(\alpha) \to (\texttt{LayerSamplerAxis I n} \to \mathbb R) \to \mathbb C$ such that: $\sum_i\|a_i\| \le A$; $\|f_{i,s}(v)\| \le 1$; each $f_{i,s}$ is Lipschitz with constant $e^{|\texttt{LayerSamplerAxis I n}| + 6Q + 12} + \Lambda$; $f_{i,s}(v) = 0$ whenever some $|v_j| > 2\rho_s$; $\sum_{\mathrm{label} : \mathcal P(\alpha) \to \mathcal L}\sum_i \|\texttt{allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i}\| \le \|N^{-1}\|\,|\mathcal L|^{|\mathcal P(\alpha)|}\,\mathrm{maskCap}\,A$; every `allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period ℓ' (f i s)` is measurable and bounded in norm by $1$; the approximation $\Phi = $ `allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f` is measurable; for every $y$ in `EuclideanJetLayers U rowTypes`, $\|\mathrm{prefactor}(y) - \Phi(y)\| \le \|N^{-1}\|\,\mathrm{maskCap}\,\varepsilon$; and for every such $y$,
--   $$\Bigl\|\mathrm{cutoff}(y)\cdot \mathbb E_{u \sim \mathrm{gridLaw}}\,\Psi_u(y) - \Phi(y)\cdot\texttt{allocatedFullGridChartModel B U b S rowSets d hb o bW e}(y)\Bigr\| \le \|\mathrm{prefactor}(y)\|\,\varepsilon_{\mathrm{grid}} + \|N^{-1}\|\,\mathrm{maskCap}\,\varepsilon\prod_a C_c(a),$$
--   where cutoff $=$ `allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr` and $\Psi_u = $ `allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (principalAxisJoin grid u (y₀|¬grid)) q ideal` (real-valued, cast to $\mathbb C$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_ideal_model` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedAffineAccurateSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B198` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedAffineAccurateSource.lean#L215

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B198

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uα

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
variable (hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
  (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
variable (hmodulus : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable (hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ)))
local notation "gridAxes" => {a // grid a}
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q label hcell x
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width
local notation "prefactor" => allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ ideal

include hperiod hM hm hR hC hchart hbudget hu₀ hmodulus hy₀ in
theorem exists_allocated_supported_affine_ideal_model
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    {εgrid : ℝ}
    (he : ∀ z : AllocatedFrozenJetRows B U b S rowTypes,
      ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * (gridDensity z : ℂ) -
        allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ εgrid)
    {Nt V Cc Hs : gridAxes → ℝ} {Lg : ℝ≥0}
    (heb : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hρp : (ρ : ℝ)⁻¹ ≤ Real.exp p) :
    let sourceRadius : ℝ≥0 := allocatedRowSlicedSiteRadius rowSets
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * sourceRadius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let A := Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset α × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset α × LayerSamplerAxis I n → Fin k) → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, 2 * (sourceRadius : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset α) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * ε) ∧
        ∀ y : EuclideanJetLayers U rowTypes,
          ‖cutoff y * ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
              (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
              allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤
            ‖prefactor y‖ * εgrid + (‖inverseNormalizer‖ * maskCap * ε) * ∏ a, Cc a := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
