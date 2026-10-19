-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedCanonical_finite_source_native_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedCanonical_finite_source_native_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:23:52.206556+00:00
-- url     : https://prove2.me/theorems/7e3dfa09-03b7-4124-9a8f-18e1c607bf58
-- title:
--   A finite chart-model source at the canonical modulus gives a twisted native correlation
-- statement:
--   Fix the section data (with universe levels $u_G, u_I, u_B, u_J$): a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` ($= \Sigma_j\,(I_j \oplus \mathrm{Fin}\,n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$; a layer-sampler scale `S : LayerSamplerScale B U b R σ` with value $L_S = $ `S.value`; natural numbers $s$ and $n_X$, with row sets $\mathrm{rowSets}_j = $ `boundedBooleanJetRows (Fin (s+1)) (j+1)` and $\mathrm{rows}_j$ their inclusions; grid is the predicate `allocatedGridAxis U b L_S` on axes; finite types $E_j$; a point $x : G \to $ `IntegerScalarCubeBox (Fin (s+1)) L_S`; a tuple $y_0$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s+1)) (allocatedPrincipalSides B U b S)`; natural numbers $q$, $d \neq 0$, $\mathrm{period} \neq 0$; $r \in \mathbb R_{\ge 0}$ with $r > 0$; $hb$: the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice V_j`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $\mathbb Z$-bases $bW_j$ of $\mathbb Z^{J_j} \cap V_j$ indexed by $E_j$; vector polynomials $p_j \in$ `VectorPolynomial (Fin nX) ℝ (J j → ℝ)` with all coefficients in $U_j$ ($hm$); a natural number $\mathrm{spatialModulus} \neq 0$ and $\mathrm{stride}, N : \mathrm{Fin}\,n_X \to \mathbb N$ with every $N_i \neq 0$, and $\mathrm{refined} = $ `residueRefinedPeriod spatialModulus stride`; a map wholeReference from labels (tuple index $\to \mathrm{Option}(\mathrm{Fin}(s+1)) \to \mathbb Z/\mathrm{refined}$) to full tuples, and one such label $\ell$; a natural number $M > 0$, an embedding $\mathrm{selection} : \mathrm{Fin}(s+1) \hookrightarrow G$ and a proof $hx$ of `GoodScalarKernelTuple selection (1/M) M x`; reals $W \ge 0$, $\tau, \xi, \mathrm{mesh}$; $\mathrm{base} : \mathrm{Fin}\,n_X \to \mathbb Z$; and a finite set $\mathrm{cells}$ of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride`. Write widths $=$ `narrowTrimmedSpatialWidths W τ ξ N`, window $=$ `spatialWindow (trimmedSpatialRootScale τ N stride) 4`, reconstruct $=$ `allocatedWholeResidueReconstruction B U b S (Fin nX) spatialModulus stride wholeReference x base ℓ`, and LongSpace, GridSpace for the tori $(\texttt{JetAmbientIndex (fun _ => Unit) J} \to \mathbb R/\mathbb Z) \times (\Sigma_j J_j \to \mathbb R/\mathbb Z)$ and $\Sigma_j J_j \to \mathbb R/\mathbb Z$.
--
--   Hypotheses: a signal $\phi : \mathbb Z^{n_X} \to \mathbb C$ with $\|\phi(u)\| \le 1$ on `integerBox N` $= \prod_i [0, N_i)$ and $\phi = 0$ outside it; $\mathrm{stride}_z > 0$; $\tau > 0$; $\xi > 0$; `allocatedPhysicalRootBudget B U b S 0` $\le W$; $\sum_z$ `selectedResidueSmoothWeight stride cells widths z` $> 0$; reals $P \ge 0$ and $D, p_{\mathrm{grid}}, v, F_{\mathrm{model}}, P_\rho, P_k, \mathrm{target}, B_{\mathrm{analytic}}, p_{\mathrm{Geometry}}, E_{\mathrm{coarse}}, p_{\mathrm{Gain}}$ all in $[0, P]$; $|G| \le p_{\mathrm{Geometry}}$, $n_X \le p_{\mathrm{Geometry}}$, $s+2 \le p_{\mathrm{Geometry}}$, $M \le e^{p_{\mathrm{Geometry}}}$, $W \le e^{p_{\mathrm{Geometry}}}L_S$; $\mathrm{spatialModulus} = $ `kernelPeriodCandidate (m+1) (goodKernelUniformCandidate selection x hx m)`; $\mathrm{mesh} = $ `allocatedEarlyRecenteredMesh (Fin nX) selection M spatialModulus pGeometry Ecoarse`; $\mathrm{stride}_i \le e^{p_{\mathrm{Geometry}}}$; $1/\tau \le e^{p_{\mathrm{Geometry}}}$; and reals $\mathrm{gain}, Z, P_{\mathrm{proj}}, \mathrm{coarseTarget}, \mathrm{lossTarget}, O_p, H_{\mathrm{grid}}$ with $e^{-p_{\mathrm{Gain}}}/2 \le \mathrm{gain}$, $1/2 \le Z$, and $p_{\mathrm{Gain}} + 32 \le P_{\mathrm{proj}}, \mathrm{coarseTarget}, E_{\mathrm{coarse}}, \mathrm{lossTarget}$ (each).
--
--   Let $A_{\mathrm{mass}}$, $A_{\mathrm{analytic}}$ be the natural numbers chosen by OpenAI's existence theorems `exists_allocatedAffineModelMass_budget m (s+1)` and `exists_allocatedAffineAnalytic_budget m (s+1)`; put $E_{\mathrm{model}} = (D + p_{\mathrm{grid}} + v + F_{\mathrm{model}} + P_\rho + P_k + \mathrm{target} + A_{\mathrm{mass}})^{A_{\mathrm{mass}}}$, $\mathrm{analytic} = (D + p_{\mathrm{grid}} + v + F_{\mathrm{model}} + P_\rho + P_k + \mathrm{target} + B_{\mathrm{analytic}} + A_{\mathrm{analytic}})^{A_{\mathrm{analytic}}}$ and $V_{\mathrm{grid}} = e^{O_p}$. The theorem asserts an implication. Its premise is: there exists $e$ assigning to each grid axis a `ScalarSiteExpansion (Finset (Fin (s+1)))` with `(e a).Bounds` $(e^{O_p}, e^{O_p}, e^{O_p}, V_{\mathrm{grid}}, e^{H_{\mathrm{grid}}})$ for every $a$, and there exist a natural number $k$, $a : K \to \mathbb C$ and $f : K \to \mathcal P(\mathrm{Fin}(s+1)) \to (\texttt{LayerSamplerAxis I n} \to \mathbb R) \to \mathbb C$ for $K = (\mathcal P(\mathrm{Fin}(s+1)) \times \texttt{LayerSamplerAxis I n} \to \mathrm{Fin}\,k)$, such that (i) $\sum_{\mathrm{label}}\sum_i\sum_{k_g}\|2^{|\mathcal P(\mathrm{Fin}(s+1))|}\cdot$ `allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i` $\cdot$ `coverSiteCoefficient e kg`$\| \le e^{E_{\mathrm{model}}}$ (labels range over $\mathcal P(\mathrm{Fin}(s+1)) \to (\prod_j \mathrm{Fin}\,n_j \to \mathbb Z/\mathrm{period}) \times (\prod_j E_j \to \mathbb Z/\mathrm{period})$ and $k_g$ over choices of one term of each `e a`); (ii) there is $L_{\mathrm{an}} \in \mathbb R_{\ge 0}$ with $L_{\mathrm{an}}\cdot\mathrm{period}\cdot V_{\mathrm{grid}}^{\#\text{grid axes}} \le e^{\mathrm{analytic}}$ and $\mathrm{period}\cdot(e^{O_p})^{\#\text{grid axes}} \le e^{\mathrm{analytic}}$, and a complex-valued analyticFactor of (label, $i \in K$, $k_g$, site, point of LongSpace $\times$ GridSpace), each $L_{\mathrm{an}}$-Lipschitz in the point and bounded in norm by $1$, with `AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm analyticFactor` (OpenAI's identity expanding the chart model at every physical row sample into products of these factors); and (iii)
--   $$Z\bigl(\mathrm{gain} - e^{-P_{\mathrm{proj}}} - e^{-\mathrm{coarseTarget}}\bigr) - e^{-E_{\mathrm{coarse}}} - e^{-\mathrm{lossTarget}} \le \mathrm{Re}\sum_{(c, w) \in \mathrm{cells} \times \mathrm{window}} \omega_c\cdot\rho_{c,w}\cdot\Phi(Y_{c,w})\cdot\Gamma(Y_{c,w}),$$
--   where $\omega_c = $ `selectedResidueCellWeight stride cells widths c`, $\rho_{c,w} = $ `allocatedRecenteredResidueWeight B U b S (Fin nX) spatialModulus stride wholeReference x hM selection hx N hW mesh base cells (physicalCubeSiteTest (integerSelfSiteTest (s+1) φ)) ℓ c w`, $Y_{c,w} = $ `physicalCubeRowSample U d rows p hm (reconstruct c w)`, $\Phi = $ `allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f` and $\Gamma = $ `allocatedFullGridChartModel B U b S rowSets d hb o bW e`.
--
--   Its conclusion is: let $C$ be the natural number chosen by `exists_canonicalSlicedNative_input_budget m (s+1) A_mass A_analytic`, $B_{\mathrm{budget}} = (P + C)^C$, $A_{\mathrm{norm}}$ the one chosen by `exists_allocatedRecenteredFactor_normalization m (s+1)`, $A_{\mathrm{native}}$ the one chosen by `exists_native_partner_of_physical_cube_mixture_all_degrees s`, $A$ the one chosen by `exists_normalizedNative_uniform_budget m A_norm A_native` (all existence theorems of OpenAI), and $\mathrm{budget} = (B_{\mathrm{budget}} + A)^A$. Then there exist twistData : `NormalizedPolynomialTwist (Fin nX) (Σ j, J j) (exp budget) (exp budget) (exp budget)` (OpenAI's structure bundling a modulus and a cover, each positive and at most $e^{\mathrm{budget}}$, a residue mask of norm $\le 1$ and an $e^{\mathrm{budget}}$-Lipschitz smooth factor of norm $\le 1$) and $F_{\mathrm{native}} : $ `integerBox N` $\to \mathbb C$ such that `NativeSampleModel (fun _ => 1) s budget (fun u => u) Fnative` is nonempty ($F_{\mathrm{native}}$ is the evaluation of a niltest of norm bound $\le 1$ and complexity $\le \mathrm{budget}$ on a rational filtered nilmanifold of degree $s$) and
--   $$e^{-\mathrm{budget}} \le \Bigl\|\mathbb E_{u \in \texttt{integerBox N}}\ \phi(u)\,\overline{\overline{\texttt{twistData.eval N p}(u)}\,F_{\mathrm{native}}(u)}\Bigr\|,$$
--   the average being the `correlation` of the uniform law on `integerBox N`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonical_finite_source_native_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonical_finite_source_native` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalProjectedNativeSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B277` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalProjectedNativeSource.lean (declaration OAI.Erdos3.VectorPolynomial.exists_allocatedCanonical_finite_source_native)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B277

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin (s + 1)) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin (s + 1))))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
local notation "window" => spatialWindow (α := Fin (s + 1)) (trimmedSpatialRootScale τ N stride) 4
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S (Fin nX) spatialModulus stride wholeReference x base label

variable [∀ i, NeZero (N i)]
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_allocatedCanonical_finite_source_native_s2
    (signal : ((Fin nX) → ℤ) → ℂ)
    (hsignal : ∀ u ∈ integerBox N, ‖signal u‖ ≤ 1)
    (hzero : ∀ u, u ∉ integerBox N → signal u = 0)
    (hstride : ∀ z, 0 < stride z) (hτ : 0 < τ) (hξ : 0 < ξ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hZmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    {P D pgrid v Fmodel Prho Pk target Banalytic pGeometry Ecoarse pGain : ℝ}
    (hP : 0 ≤ P) (hD : D ∈ Icc 0 P) (hgrid : pgrid ∈ Icc 0 P) (hv : v ∈ Icc 0 P)
    (hFmodel : Fmodel ∈ Icc 0 P) (hPrho : Prho ∈ Icc 0 P) (hPk : Pk ∈ Icc 0 P)
    (htarget : target ∈ Icc 0 P) (hBanalytic : Banalytic ∈ Icc 0 P)
    (hGeometry : pGeometry ∈ Icc 0 P) (hEcoarse : Ecoarse ∈ Icc 0 P)
    (hpGain : pGain ∈ Icc 0 P)
    (hGGeometry : (Fintype.card G : ℝ) ≤ pGeometry)
    (hXGeometry : (nX : ℝ) ≤ pGeometry) (hdimGeometry : ((s + 2 : ℕ) : ℝ) ≤ pGeometry)
    (hMGeometry : (M : ℝ) ≤ Real.exp pGeometry)
    (hWGeometry : W ≤ Real.exp pGeometry * S.value)
    (hcanonical : spatialModulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
    (hmeshEarly : mesh = allocatedEarlyRecenteredMesh (Fin nX) selection M spatialModulus pGeometry Ecoarse)
    (hstrideGeometry : ∀ i, (stride i : ℝ) ≤ Real.exp pGeometry)
    (hτGeometry : 1 / τ ≤ Real.exp pGeometry)
    {gain Z Pproj coarseTarget lossTarget Op Hgrid : ℝ}
    (hgain : Real.exp (-pGain) / 2 ≤ gain) (hZ : 1 / 2 ≤ Z)
    (hPproj : pGain + 32 ≤ Pproj) (hcoarseTarget : pGain + 32 ≤ coarseTarget)
    (hEcoarseGain : pGain + 32 ≤ Ecoarse) (hlossTarget : pGain + 32 ≤ lossTarget) :
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m (s + 1))
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m (s + 1))
    let Emodel := (D + pgrid + v + Fmodel + Prho + Pk + target + Amass) ^ Amass
    let analytic := (D + pgrid + v + Fmodel + Prho + Pk + target + Banalytic + Aanalytic) ^ Aanalytic
    let Vgrid : ℝ≥0 := ⟨Real.exp Op, Real.exp_nonneg _⟩
    (∃ e : {a // grid a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))),
      (∀ z, (e z).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op) Vgrid (Real.exp Hgrid)) ∧
      ∃ k : ℕ, ∃ (a : (Finset (Fin (s + 1)) × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset (Fin (s + 1)) × LayerSamplerAxis I n → Fin k) →
          Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ label : Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
          ∑ i, ∑ kg, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin (s + 1))) *
            allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
            coverSiteCoefficient e kg‖) ≤ Real.exp Emodel ∧
        (∃ Lanalytic : ℝ≥0,
          ((Lanalytic * ((period : ℝ≥0) * Vgrid ^ Fintype.card {a // grid a}) : ℝ≥0) : ℝ) ≤
            Real.exp analytic ∧
          (period : ℝ) * (Real.exp Op) ^ Fintype.card {a // grid a} ≤ Real.exp analytic ∧
          ∃ analyticFactor : (Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) ×
              (∀ j, E j → ZMod period))) →
              (Finset (Fin (s + 1)) × LayerSamplerAxis I n → Fin k) → (∀ z, (e z).Term) →
              Finset (Fin (s + 1)) → LongSpace × GridSpace → ℂ,
            (∀ label i kg site, LipschitzWith Lanalytic (analyticFactor label i kg site)) ∧
            (∀ label i kg site z, ‖analyticFactor label i kg site z‖ ≤ 1) ∧
            AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm analyticFactor) ∧
        Z * (gain - Real.exp (-Pproj) - Real.exp (-coarseTarget)) -
          Real.exp (-Ecoarse) - Real.exp (-lossTarget) ≤
          (∑ z : cells × window, (selectedResidueCellWeight stride cells widths z.1 : ℂ) *
            allocatedRecenteredResidueWeight (τ := τ) B U b S (Fin nX) spatialModulus stride wholeReference x hM selection hx
              N hW mesh base cells (physicalCubeSiteTest (integerSelfSiteTest (s + 1) signal)) label z.1 z.2.val *
            (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
              (physicalCubeRowSample U d rows p hm (reconstruct z.1.val z.2.val)) *
            allocatedFullGridChartModel B U b S rowSets d hb o bW e
              (physicalCubeRowSample U d rows p hm (reconstruct z.1.val z.2.val)))).re) →
    let C := Classical.choose (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)
    let Bbudget := (P + C) ^ C
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun u : integerBox N => u.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun u => signal u.val) (fun u => star (twistData.eval N p u.val) * Fnative u)‖ := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
