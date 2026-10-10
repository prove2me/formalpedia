-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_supported_affine_uniform_physical_source
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_uniform_physical_source
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T10:24:16.781019+00:00
-- url     : https://prove2.me/theorems/f45a5fcc-66e1-4a97-bb77-d2c5ad6267ec
-- title:
--   Grid site expansion and chart model with a physical expansion, uniformly in the cube point
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` ($= \Sigma_j\, (I_j \oplus \mathrm{Fin}\,n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$; a layer-sampler scale `S : LayerSamplerScale B U b R σ` with value $L_S = $ `S.value`; a natural number $\mathrm{dim}$, with the row sets $\mathrm{rowSets}_j = $ `boundedBooleanJetRows (Fin dim) (j+1)` (all subsets of $\mathrm{Fin}\,\mathrm{dim}$ of size at most $j+1$), row types $\mathrm{rowTypes}_j = \{t : t \in \mathrm{rowSets}_j\}$ and $\mathrm{rows}_j$ the inclusion into $\mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim})$; finite types $E_j$; a natural number $q$; $r \in \mathbb R_{\ge 0}$ with $r > 0$; $hb$: the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice V_j` for every $j$; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $\mathbb Z$-bases $bW_j$ of $\mathbb Z^{J_j} \cap V_j$ indexed by $E_j$; $R_j > 0$ for every $j$; reals $C_j \ge 0$ with $\|(\texttt{normalizedOrthogonalChart}\ V_j\ b_j)^{-1}v\| \le C_j\|v\|$ and $(|\mathrm{rowSets}_j|+1)\,|\mathcal P(\mathrm{Fin}\,\mathrm{dim})|\,C_j(|I_j|+1)\,2rR_j \le 1/4$; $\rho \in \mathbb R_{\ge 0}$; real functions $\mathrm{center}, \mathrm{width}$ on `PrincipalAxisParameter (fun a => ¬ grid a)`, where grid is the predicate `allocatedGridAxis U b L_S` on axes; $\sigma_j > 0$ for every $j$; natural-valued $H, \mathrm{step}$ and integer-valued $c$ on `PrincipalTupleIndex B (layerSamplerDegree I n)` with $H > 0$ and each progression $\{c_t + \mathrm{step}_t k : 0 \le k < H_t\}$ contained in $[0, \texttt{allocatedPrincipalSides B U b S t})$ ($hsubset$); and a label $\ell :$ tuple index $\to \mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z/q$ with $hcell$: the tuples whose residues mod $q$ equal $\ell$ have positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH`. Let gridLaw be `containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c _ hH hsubset q ℓ hcell grid` (a finite probability law on grid-axis tuples) and ideal $=$ `allocatedRowSlicedIdeal B U b S rowSets ρ center width`.
--
--   Hypotheses of the theorem: $C_{\mathrm{forward}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$ with $\|\texttt{normalizedOrthogonalChart}\ V_j\ b_j\ v\| \le C_{\mathrm{forward}}(j)\|v\|$; $K \in \mathbb R_{\ge 0}$ with $R_j^{-1} \le K$; $Q_{\mathrm{grid}} \in \mathbb R_{\ge 0}$ with $8\,(|\texttt{layerIntegerPrincipalSlots B}\ (\texttt{allocatedGridIntegerAxis B U b S a})| + 1) \le Q_{\mathrm{grid}}$ for every grid axis $a$; $q > 0$; a real $\delta_g > 0$ with $\delta_g \cdot \texttt{allocatedPrincipalSides B U b S}(t) \le H_t$ for every $t$; a natural number $T_g \ge (\mathrm{dim}+1)q/\delta_g$; $\mathrm{step}_t > 0$ for every $t$; $A_g \in \mathbb R_{\ge 0}$ a Lipschitz constant of `Real.smoothTransition`; a real $P_g \ge 1$ with `scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1` $\le P_g$, `scalarCubePrimitiveEnvelope (Fin dim) Ag 1 0 q` $\le P_g$ (explicit reals defined by OpenAI) and $\mathrm{step}_t\, q \le P_g$ for every $t$; for every $j$ and $i \in \mathrm{Fin}\,n_j$, `positiveModerateSpectrumBlockCount j |rowSets j| ((layerTailDegree m + 1)|rowSets j|)` $\le |B_{(j, \mathrm{inr}\ i)}|$ and `uniformSpectrumBlockCount j |rowSets j| ((j+1)|rowSets j|)` $\le |B_{(j, \mathrm{inr}\ i)}|$; reals $D_g, v_g, w_g, t_g, p_g, E_g, \varepsilon_{\mathrm{grid}}$ with $D_g, v_g, w_g, t_g, p_g, E_g \ge 0$, $\mathrm{dim} \le D_g$, $j+1 \le D_g$, $|\mathrm{rowSets}_j| \le D_g$, `layerTailDegree m` $+1 \le D_g$, $|B_{(j,\mathrm{inr}\ i)}| \le D_g$, $R_j \le e^{v_g}$, $R_j^{-1} \le e^{v_g}$, $\delta_g^{-1} \le e^{w_g}$, $T_g \le e^{t_g}$, $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| \le e^{v_g}$, $P_g \le e^{p_g}$, (number of grid axes) $\le D_g$, $\varepsilon_{\mathrm{grid}} > 0$, $\varepsilon_{\mathrm{grid}}^{-1} \le e^{E_g}$ and $\sigma_j \le 1$ (stated twice); $T : \mathrm{Fin}\,m \to \mathbb R$ with $T_j \ge 0$, `partitionedIdealRadius (Fin dim) m` $+1 \le T_j$, $|\texttt{BoundedCoefficientExponent}\dots(j+1)|\cdot 2^{\mathrm{dim}}(\mathrm{dim}+1)^{j+1} \le T_j$ and $|\mathrm{rowSets}_j|\,T_j \le r$; $0 < \rho \le 1$; $|\mathrm{center}_i| + |\mathrm{width}_i| \le 1$; and reals $\varepsilon > 0$, $P_{\mathrm{long}} \ge 0$ with $2\rho_s \le e^{P_{\mathrm{long}}}$, $\varepsilon^{-1} \le e^{P_{\mathrm{long}}}$, $\rho^{-1} \le e^{P_{\mathrm{long}}}$, where $\rho_s = $ `allocatedRowSlicedSiteRadius rowSets`.
--
--   Put $p = $ `slicedGridGeometryLog Dg vg wg tg` $+ p_g$; $L_j(E) = $ `slicedGridSiteLog j |rowSets j| ((layerTailDegree m + 1)|rowSets j|) ((j+1)|rowSets j|) Dg p E`; $C_p = \sum_j (L_j(0) + D_g(v_g+1))$; $E_g' = $ `uniformProductAccuracyLog Dg Cp Eg` $+ D_g(v_g+1) + 1$; and $O_p = \sum_j \bigl(\texttt{siteExponentialOutputLog}\ |\mathcal P(\mathrm{Fin}\,\mathrm{dim})|\ (L_j(E_g')) + (D_g+1)(v_g+1)\bigr)$ (all explicit real expressions defined by OpenAI). The conclusion is: there exists $e$ assigning to each grid axis a `ScalarSiteExpansion (Finset (Fin dim))` (a finite family of terms with periods, complex coefficients and factor functions) with `(e a).Bounds` $(e^{O_p}, e^{O_p}, e^{O_p}, e^{O_p}, e^{\texttt{slicedGridGeometryLog Dg vg wg tg} + D_g + v_g + 8})$ for every $a$ (at most $e^{O_p}$ terms, positive periods $\le e^{O_p}$, coefficient $\ell^1$-norm $\le e^{O_p}$, factors of norm $\le 1$, $e^{O_p}$-Lipschitz and vanishing for $|x|$ at least the last bound), such that the following holds.
--
--   For every $x : G \to $ `IntegerScalarCubeBox (Fin dim) L_S`, every tuple $y_0$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)` and all natural numbers $d \neq 0$, $\mathrm{period} \neq 0$ with $\mathrm{period} \mid d$, if $\mathrm{period}\cdot\mathbb Z^{\mathrm{rowTypes}_j}$ is contained in the range of `scalarKernelIntegerJet x (j+1) (rows j)` for every $j$, if $M \ge 1$ is a real with $0 \le$ `allocatedIntegerKernelMask B U b S x rows j q (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x (y₀|grid) rows j (y₀|¬grid)) q) z` $\le M$ for all $j, z$, if the restriction of $y_0$ to the grid axes has nonzero gridLaw weight, if $q\cdot\mathbb Z^{\mathrm{rowTypes}_j}$ is contained in the range of `scalarKernelIntegerJet x (j+1) (rows j)` for every $j$, and if each $y_0(t)$ satisfies `IntegerScalarCube (allocatedPrincipalSides B U b S t)`, then — writing $Q = $ `idealSiteLogBudget (card (Σ a, rowTypes a.1)) dim Plong`, $\Lambda = |\texttt{LayerSamplerAxis I n}|\cdot\texttt{normalizedSiteCutoffBound}/(2\rho_s)$, $A = \exp(|\mathcal P(\mathrm{Fin}\,\mathrm{dim})|\,|\texttt{LayerSamplerAxis I n}|\,(4Q+8) + Q)$, $\mathrm{maskCap} = M^{|\texttt{LayerSamplerAxis I n}|}\cdot$ `coefficientDeckPeriodCap rowTypes E period`, $N = $ `allocatedProductIdealNormalizer B U b S rowSets` and $\mathcal L = (\prod_j \mathrm{Fin}\,n_j \to \mathbb Z/\mathrm{period}) \times (\prod_j E_j \to \mathbb Z/\mathrm{period})$ — there exist a natural number $k$ with $k \le e^{4Q+8}$ and $|K| \le \exp(|\mathcal P(\mathrm{Fin}\,\mathrm{dim})|\,|\texttt{LayerSamplerAxis I n}|\,(4Q+8))$ for $K = (\mathcal P(\mathrm{Fin}\,\mathrm{dim}) \times \texttt{LayerSamplerAxis I n} \to \mathrm{Fin}\,k)$, and $a : K \to \mathbb C$, $f : K \to \mathcal P(\mathrm{Fin}\,\mathrm{dim}) \to (\texttt{LayerSamplerAxis I n} \to \mathbb R) \to \mathbb C$ with:
--
--   - $\sum_i\|a_i\| \le A$; $\|f_{i,s}(v)\| \le 1$; each $f_{i,s}$ is $(e^{|\texttt{LayerSamplerAxis I n}| + 6Q + 12} + \Lambda)$-Lipschitz; $f_{i,s}(v) = 0$ whenever some $|v_j| > 2\rho_s$;
--   - $\sum_{\mathrm{label} : \mathcal P(\mathrm{Fin}\,\mathrm{dim}) \to \mathcal L}\sum_i\|\texttt{allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i}\| \le \|N^{-1}\|\,|\mathcal L|^{|\mathcal P(\mathrm{Fin}\,\mathrm{dim})|}\,\mathrm{maskCap}\,A$;
--   - every `allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period ℓ' (f i s)` is measurable with norm $\le 1$ everywhere, and $\Phi = $ `allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f` is measurable;
--   - for every $y$ in `EuclideanJetLayers U rowTypes`, $\|\texttt{allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ ideal}(y) - \Phi(y)\| \le \|N^{-1}\|\,\mathrm{maskCap}\,\varepsilon$;
--   - for every such $y$, $\bigl\|\mathbb E_{u \sim \mathrm{gridLaw}}\Psi_u(y) - \Phi(y)\cdot\texttt{allocatedFullGridChartModel B U b S rowSets d hb o bW e}(y)\bigr\| \le \|N^{-1}\|\,\mathrm{maskCap}\,\bigl(\rho^{-\kappa}\varepsilon_{\mathrm{grid}} + \varepsilon\,(e^{O_p})^{\#\text{grid axes}}\bigr)$, where $\Psi_u = $ `allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (principalAxisJoin grid u (y₀|¬grid)) q ideal` and $\kappa$ is the number of pairs of a non-grid axis and a row at its layer;
--   - for every type $X$, every family of vector polynomials $\mathrm{poly}_j \in$ `VectorPolynomial X ℝ (J j → ℝ)` of total degree at most $j+1$ (`DegreeLE 1 (j+1)`) whose coefficients all lie in $U_j$ ($hm$), writing $L_{\mathrm{coord}} = K\sum_j C_{\mathrm{forward}}(j)|J_j|$, $L_{\mathrm{long}} = \bigl(|\texttt{LayerSamplerAxis I n}|\cdot\texttt{normalizedSiteCutoffBound}/(2r)\bigr)L_{\mathrm{coord}} + \max\bigl((e^{|\texttt{LayerSamplerAxis I n}|+6Q+12} + \Lambda)\,L_{\mathrm{coord}}\,\mathrm{period},\ 4\,\mathrm{period}\bigr)$, $L_{\mathrm{prim}} = e^{O_p}$ and $L_{\mathrm{grid}} = \max\bigl(\#\text{grid axes}\cdot L_{\mathrm{prim}}\, Q_{\mathrm{grid}}\, L_{\mathrm{coord}}\, L_{\mathrm{prim}}^{\#\text{grid axes}},\ 4L_{\mathrm{prim}}^{\#\text{grid axes}}\bigr)$, there exists a function $g$ of a label $\mathcal P(\mathrm{Fin}\,\mathrm{dim}) \to \mathcal L$, an index $i \in K$, a choice of one term of each `e a`, a site $t \in \mathcal P(\mathrm{Fin}\,\mathrm{dim})$ and a point of $\bigl((\texttt{JetAmbientIndex (fun _ => Unit) J} \to \mathbb R/\mathbb Z) \times (\Sigma_j J_j \to \mathbb R/\mathbb Z)\bigr) \times (\Sigma_j J_j \to \mathbb R/\mathbb Z)$, with complex values, such that each $g(\mathrm{label}, i, k_g, t, \cdot)$ is $(L_{\mathrm{long}} + L_{\mathrm{grid}})$-Lipschitz and bounded in norm by $1$, and `AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f poly hm g` holds (OpenAI's identity: for every integer sample $v : X \to (\mathrm{Unit} \oplus \mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z$, the product $\Phi\cdot$ `allocatedFullGridChartModel … e` at the physical row sample of $v$ equals $\sum_{\mathrm{label}}\sum_i\sum_k 2^{|\mathcal P(\mathrm{Fin}\,\mathrm{dim})|}\,$(masked coefficient)$\,\cdot\,$`coverSiteCoefficient e k`$\,\cdot\prod_s g(\mathrm{label}, i, k, s, \cdot)$ evaluated at physical inputs built from $v$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_uniform_physical_source` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedAffineAccurateSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B198` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedAffineAccurateSource.lean#L733

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

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


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

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


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
variable (hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
  (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
variable (hmodulus : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable (hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ)))
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width

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

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


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
variable (hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
  (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
variable (hmodulus : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable (hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ)))
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uα

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
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
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


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

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j : Fin m, ((boundedBooleanJetRows (Fin dim) (j.val + 1)).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := (Fin dim)) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := (Fin dim)) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
local notation "gridAxes" => {a // grid a}
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width

include hR hC hchart hbudget in
theorem exists_allocated_supported_affine_uniform_physical_source
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (Qgrid : ℝ≥0) (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Qgrid)
    (hq : 0 < q) {δg : ℝ} (hδg : 0 < δg)
    (hdenseg : ∀ tg, δg * allocatedPrincipalSides B U b S tg ≤ (H tg : ℝ))
    (Tg : ℕ) (hQTg : (((Fintype.card (Fin dim) + 1) * q : ℕ) : ℝ) / δg ≤ Tg)
    (hstep : ∀ tg, 0 < step tg)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition) (Pg : ℝ) (hPg : 1 ≤ Pg)
    (hcP : scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) Ag 1 0 q ≤ Pg)
    (hstride : ∀ tg, ((step tg * q : ℕ) : ℝ) ≤ Pg)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg tg pg Eg εgrid : ℝ}
    (hDg : 0 ≤ Dg) (hvg : 0 ≤ vg) (hwg : 0 ≤ wg) (htg : 0 ≤ tg) (hpg : 0 ≤ pg) (hEg : 0 ≤ Eg)
    (hcube : (Fintype.card (Fin dim) : ℝ) ≤ Dg) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin dim) (j.val + 1)).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : δg⁻¹ ≤ Real.exp wg) (hTg : (Tg : ℝ) ≤ Real.exp tg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (hPp₀ : Pg ≤ Real.exp pg) (haxes : (Fintype.card gridAxes : ℝ) ≤ Dg)
    (hεgrid : 0 < εgrid) (hεgridEg : εgrid⁻¹ ≤ Real.exp Eg) (hσgrid : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j) (hTideal : ∀ j, partitionedIdealRadius (Fin dim) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin dim) * ((Fintype.card (Fin dim) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (boundedBooleanJetRows (Fin dim) (j.val + 1)).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {ε Plong : ℝ} (hε : 0 < ε) (hPlong : 0 ≤ Plong)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Plong)
    (hεp : ε⁻¹ ≤ Real.exp Plong) (hρp : (ρ : ℝ)⁻¹ ≤ Real.exp Plong) :
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    let L := fun j : Fin m => fun e : ℝ => slicedGridSiteLog j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) Dg p e
    let Cp := ∑ j, (L j 0 + Dg * (vg + 1))
    let Eg' := uniformProductAccuracyLog Dg Cp Eg + Dg * (vg + 1) + 1
    let Op := ∑ j, (siteExponentialOutputLog (Fintype.card (Finset (Fin dim))) (L j Eg') + (Dg + 1) * (vg + 1))
    ∃ e : gridAxes → ScalarSiteExpansion.{0,0} (Finset (Fin dim)),
      (∀ a, (e a).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op)
        ⟨Real.exp Op, Real.exp_nonneg _⟩ (Real.exp (slicedGridGeometryLog Dg vg wg tg + (Dg + vg + 8)))) ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
        (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
        (d period : ℕ) [NeZero d] [NeZero period] (_hdiv : period ∣ d)
        (_hperiod : ∀ j : Fin m, integerScalarLattice {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)} (period : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)} → Finset (Fin dim))).mulVecLin.range)
        {M : ℝ} (_hM : 1 ≤ M)
        (_hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
          (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)} → Finset (Fin dim))) j q
          (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
            (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
            (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)} → Finset (Fin dim))) j
            (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
          allocatedIntegerKernelMask B U b S x
            (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)} → Finset (Fin dim))) j q
            (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
              (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
              (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)} → Finset (Fin dim))) j
              (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

        (_hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
          (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
        (_hmodulus : ∀ j : Fin m, integerScalarLattice {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)} (q : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)} → Finset (Fin dim))).mulVecLin.range)
        (_hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ))),
    let sourceRadius : ℝ≥0 := allocatedRowSlicedSiteRadius rowSets
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * sourceRadius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card (Fin dim)) Plong
    let A := Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, 2 * (sourceRadius : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset (Fin dim)) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * ε) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
              (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
              allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤
            ‖inverseNormalizer‖ * maskCap *
              ((ρ⁻¹ ^ Fintype.card (Σ a : {a // ¬grid a}, rowTypes a.val.1) : ℝ≥0) * εgrid +
                ε * ∏ _a : gridAxes, Real.exp Op)) ∧
        ∀ {X : Type*} (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
          (hm : ∀ j e, coefficients (poly j) e ∈ U j),
          let Lcoord : ℝ≥0 := K * ∑ j, Cforward j * Fintype.card (J j)
          let Llong : ℝ≥0 := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
            max ((⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) * Lcoord * period) (4 * period)
          let Lprimitive : ℝ≥0 := ⟨Real.exp Op, Real.exp_nonneg Op⟩
          let Lgrid : ℝ≥0 := max ((((Fintype.card gridAxes : ℝ≥0) * Lprimitive) * Qgrid) *
            Lcoord * Lprimitive ^ Fintype.card gridAxes) (4 * Lprimitive ^ Fintype.card gridAxes)
          ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
              (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → (∀ a, (e a).Term) → Finset (Fin dim) →
              (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
                ((Σ j, J j) → UnitAddCircle)) → ℂ,
            (∀ label i kg t, LipschitzWith (Llong + Lgrid) (g label i kg t)) ∧
            (∀ label i kg t z, ‖g label i kg t z‖ ≤ 1) ∧
            AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f poly hm g := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
