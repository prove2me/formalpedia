-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_fixedSpatialSliceNativeAmbientRationalMean_comparison_s2
-- name    : OAI.Erdos3.VectorPolynomial.fixedSpatialSliceNativeAmbientRationalMean_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:06:44.186988+00:00
-- url     : https://prove2.me/theorems/7d8b1d92-ebbf-4f43-adfd-3de5190a6311
-- title:
--   The twisted physical mean of the forecast target is close to its rational grid mean
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$ and a finite type $X$ (in `Type`); finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` ($= \Sigma_j\,(I_j \oplus \mathrm{Fin}\,n_j)$); finite types $J_j$ (in `Type`), real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$, $\sigma_j > 0$; a layer-sampler scale `S : LayerSamplerScale B U basis R σ` with value $L_S = $ `S.value`; short is the predicate `allocatedShortAxis U basis L_S` on axes (axes $(j, \mathrm{inr}\,i)$ with `basisAxisScale (basis j) i` $\le L_S^{j+1}$), selected $=$ `allocatedShortIntegerSelection U basis L_S`, and Out $= \Sigma$ `AllocatedCongruenceRankOutput X Eout short`; a finite probability law $\mathrm{law}$ on `PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)` (the principal tuples); real functions $\mathrm{lowerSlice}, \mathrm{widthSlice}$ on pairs of a non-short axis $a$ and an element of $B_a \times \mathrm{Fin}(\texttt{layerSamplerDegree I n}\ a)$; sampler arrays `sample : CoefficientSamplerArrays I n`; a point $x_{\mathrm{ref}} : G \to $ `IntegerScalarCubeBox Empty L_S`; a finite type $\Omega$ and finite types $E^{\mathrm{out}}_j$; for each principal tuple a finite probability law $\mathrm{active}(i)$ on $\Omega$ and a map $Y(i) : \Omega \to \mathrm{Out} \to \mathbb Z$; a natural number $N \neq 0$ and a real $\mathrm{gridVolume}$; $\mathrm{base} : X \to \mathbb Z$, $\mathrm{physicalN} : X \to \mathbb N$ and a real $\tau$; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $hb$: the $\mathbb Z$-span of $\mathrm{basis}_j$ is `projectedIntegerLattice V_j`; $\mathbb Z$-bases $bW_j$ of $\mathbb Z^{J_j} \cap V_j$ indexed by $E^{\mathrm{out}}_j$; reals $p_w, c_w$, $L_w \in \mathbb R_{\ge 0}$ and $W_{\mathrm{test}}$ : `NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw` (OpenAI's structure bundling a positive modulus $\le p_w$, a positive cover $\le c_w$, a residue mask of norm $\le 1$ and an $L_w$-Lipschitz smooth factor of norm $\le 1$); the assumption that each $\mathbb Z^{J_j} \cap V_j$ is a full lattice in $V_j$; additively left-invariant probability measures $\nu_j$ on $V_j/(\mathbb Z^{J_j} \cap V_j)$; a compact-space instance on `EuclideanJetLayers U (fun _ => Unit)`; a finite type $T_{\mathrm{geo}}$ and an equivalence $e : G \simeq X \oplus (X \oplus T_{\mathrm{geo}})$; reals $\mathrm{rootBudget}, \mathrm{rootLength}$ and $z : \mathrm{Option}\,G \times X \to \mathbb R$; real functions $\mathrm{lower}_G, \mathrm{width}_G$ on $G$ with $\mathrm{width}_G \neq 0$; $h_0, h_1$: the integer matrices `fixedSpatialKernelBlock e rootBudget rootLength z false` and `… true` have nonzero determinant; and $hB$: $|B_a| \ge 4$ for every non-short axis $a$. Write density $=$ `fixedSpatialKernelSliceOriginalForecastDensity B U basis S e rootBudget rootLength z lowerG widthG h0 h1 hwGne hB lowerSlice widthSlice sample` (a real function defined by OpenAI) and $\kappa = $ `forecastGeometricJacobian U basis R L_S gridVolume τ` (a real constant, cast to $\mathbb C$). The theorem includes $hR$, $h\sigma$, $\nu$, the compact-space instance and the lattice assumption among its hypotheses.
--
--   Hypotheses: for every $j$, `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)`; a real $\delta_P > 0$ with $\delta_P \le \mathrm{widthSlice}$, $0 \le \mathrm{lowerSlice}$, $|\mathrm{lowerSlice}| + |\mathrm{widthSlice}| \le 1$ everywhere; $0 \le \mathrm{lower}_G$, $0 \le \mathrm{width}_G$, $\mathrm{lower}_G + \mathrm{width}_G \le 1$; $\sigma_{a.1} \le 1$ for every short integer axis $a$; $r \in \mathbb R_{\ge 0}$ with $0 < r$, $3 \le r$ and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| \le r$; reals $C_j \ge 0$ with $\|(\texttt{normalizedOrthogonalChart}\ V_j\ \mathrm{basis}_j)^{-1}v\| \le C_j\|v\|$ and $C_j(|I_j|+1)\,2rR_j \le 1/4$; $\mathrm{rootBudget}, \mathrm{rootLength} \ge 0$ with $|G|\,\mathrm{rootLength} \le \mathrm{rootBudget}$; $|z| \le 1$; $\tau > 0$; $2\,$`spatialTrimMargin τ physicalN i` $\le \mathrm{physicalN}_i$ (where `spatialTrimMargin τ N i` $= \lceil \tau N_i/4\rceil$); $\mathrm{base} \in$ `trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN)`; a natural number $q \neq 0$ with $q \mid N$; $m > 0$; $W_{\mathrm{test}}.\mathrm{modulus} \mid q$ and $W_{\mathrm{test}}.\mathrm{cover} \mid q$; $\mathrm{gridVolume} > 0$; a finite type $F_{\mathrm{index}}$, reals $p_f, c_f$, $L_f \in \mathbb R_{\ge 0}$, twists $F_i$ : `NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf`, coefficients $c_i \in \mathbb C$ and a real $\delta$ such that for every family of vector polynomials $\mathrm{poly}'_j \in$ `VectorPolynomial X ℝ (J j → ℝ)` with coefficients in $U_j$ and every $u \in \mathbb Z^X$,
--   $$\Bigl\|\kappa\cdot\Theta(\mathrm{poly}', u) - \sum_i c_i\,(F_i).\mathrm{eval}\ \mathrm{physicalN}\ \mathrm{poly}'\ u\Bigr\| \le \delta,$$
--   where $\Theta(\mathrm{poly}', u) = $ `forecastLawDensityPhysicalTarget B U basis S law density selected sample xref active Y N gridVolume base physicalN τ o hb bW poly' hmem u` (a complex number defined by OpenAI); vector polynomials $\mathrm{poly}_j$ of total degree at most $j+1$ with coefficients in $U_j$; reals $P, E \ge 0$, $R_{\mathrm{rank}}$, $M$ with $|X| \le P$, $|\Sigma_j J_j| \le P$, $L_w\max(1, c_f) + L_f\max(1, c_w) \le e^{P}$, $W_{\mathrm{test}}.\mathrm{cover}\cdot F_i.\mathrm{cover} \le e^{P}$ and $W_{\mathrm{test}}.\mathrm{modulus}\cdot F_i.\mathrm{modulus} \le e^{P}$ for all $i$, $\sum_i\|c_i\| \le M$, $\exp((\max(P,E) + A)^A) \le \mathrm{physicalN}_i$ and $\le R_{\mathrm{rank}}$ where $A = $ `nativeForecastAmbientExponent m` (a natural number chosen by OpenAI), and `HasLayerSamplingRank (j+1) physicalN R_rank (U j) (poly j)` for every $j$; a natural number $\mathrm{cutoff} > 0$; reals $D \ge 0$, $P_{\mathrm{decay}} \ge |\mathrm{Out}| + 2$ and $\delta_{\mathrm{grid}} \in [0,1]$ such that for every principal tuple $i$ and every additive character $\chi$ of $\mathrm{Out} \to \mathbb Z/N$, $\|\texttt{finiteImageCharacteristic}(\mathrm{active}(i), Y(i) \bmod N, \chi)\| \le D\cdot\mathrm{orderOf}(\chi)^{-P_{\mathrm{decay}}}$ (the expectation of $\chi(Y(i)(x) \bmod N)$ under $\mathrm{active}(i)$), and $q\cdot\mathrm{cutoff}/$`forecastJointGridScale U basis R L_S physicalN τ j` $\le \delta_{\mathrm{grid}}$ for every $j$.
--
--   Let frame $=$ `fixedSpatialKernelSliceFrame rootBudget rootLength z lowerG widthG`; let $C_{\mathrm{grid}} = $ `fixedSpatialOriginalForecastCap B (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame true _) hδP` and $L_{\mathrm{grid}} = $ `fixedSpatialOriginalForecastLip B (fixedSpatialKernelBlockEquiv … false _) (fixedSpatialKernelBlockEquiv … true _) hδP` (explicit nonnegative constants defined by OpenAI); $K_{\mathrm{grid}} = L_w\max(|\tau/8|, \texttt{forecastNativeAmbientLip U basis o R})$; grid $=$ `forecastInactiveFixedOutput B U basis S selected (allocatedOriginalSampleInactiveCoefficients B selected sample) xref`; and test $=$ `Wtest.forecastShortGridTest U basis L_S hb o bW R q hm hperiod hcover (fun a => base a / physicalN a) τ`. Then
--   $$\Bigl\|\mathbb E_{u \in \texttt{integerBox physicalN}} W_{\mathrm{test}}.\mathrm{eval}(\mathrm{physicalN}, \mathrm{poly}, u)\cdot\kappa\,\Theta(\mathrm{poly}, u) - \sum_g \mathbb E_{r : \mathrm{Out} \to \mathbb Z/N} \frac{\texttt{rationalInactiveForecast law active grid Y N gridVolume g r}}{\mathrm{gridVolume}} \int \mathrm{test}(g, r \bmod q, y)\,d\lambda_{\mathrm{density}}(y)\Bigr\|$$
--   $$\le 2\delta + M e^{-E} + \texttt{forecastJointGridError}\ |\mathrm{Out}|\ |X \oplus \texttt{AllocatedActiveIntegerAxis U basis L_S}|\ |\Sigma_j I_j|\ \mathrm{cutoff}\ D\ L_{\mathrm{grid}}\ C_{\mathrm{grid}}\ K_{\mathrm{grid}}\ \delta_{\mathrm{grid}},$$
--   where the sum over $g$ is a `tsum`, $r \bmod q$ is the image of $r$ under $\mathbb Z/N \to \mathbb Z/q$, and $\lambda_{\mathrm{density}}$ is Lebesgue measure with density density (`realDensityMeasure volume density`).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.fixedSpatialSliceNativeAmbientRationalMean_comparison_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.fixedSpatialSliceNativeAmbientRationalMean_comparison` (in `lean/OAI/Combinatorics/Progressions/Geometry/FixedSpatialSliceNativeAmbientRationalComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B266` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/FixedSpatialSliceNativeAmbientRationalComparison.lean (declaration OAI.Erdos3.VectorPolynomial.fixedSpatialSliceNativeAmbientRationalMean_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B266

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} {X : Type} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (lowerSlice widthSlice : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω → Sigma (AllocatedCongruenceRankOutput X Eout
    (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (gridVolume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {pw cw : ℝ} {Lw : ℝ≥0}
variable (Wtest : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable {Tgeo : Type*} [Fintype Tgeo]
variable (e : G ≃ X ⊕ (X ⊕ Tgeo)) (rootBudget rootLength : ℝ) (z : Option G × X → ℝ)
variable (lowerG widthG : G → ℝ)
variable (hwGne : ∀ g, widthG g ≠ 0)
variable (h0 : (fixedSpatialKernelBlock e rootBudget rootLength z false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e rootBudget rootLength z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
  4 ≤ Fintype.card (B a.val))
local notation "density" => fixedSpatialKernelSliceOriginalForecastDensity B U basis S e rootBudget
  rootLength z lowerG widthG h0 h1 hwGne hB lowerSlice widthSlice sample
local notation "κ" => ((forecastGeometricJacobian (X := X) (I := I) U basis R S.value gridVolume τ : ℝ) : ℂ)

include hR hσ ν hcompact hlattice in
theorem fixedSpatialSliceNativeAmbientRationalMean_comparison_s2
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {δP : ℝ} (hδP : 0 < δP)
    (hwP : ∀ a p, δP ≤ widthSlice a p) (hlP : ∀ a p, 0 ≤ lowerSlice a p)
    (hwidthP : ∀ a p, |lowerSlice a p| + |widthSlice a p| ≤ 1)
    (hlG : ∀ g, 0 ≤ lowerG g) (hwG : ∀ g, 0 ≤ widthG g)
    (hcontainedG : ∀ g, lowerG g + widthG g ≤ 1)
    (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hW : 0 ≤ rootBudget) (hL : 0 ≤ rootLength)
    (hsize : (Fintype.card G : ℝ) * rootLength ≤ rootBudget) (hz : ∀ a, |z a| ≤ 1)
    (hτ : 0 < τ) (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
    (hbase : base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
    (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : Wtest.modulus ∣ q) (hcover : Wtest.cover ∣ q) (hV : 0 < gridVolume)
    {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
    (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
    (c : Findex → ℂ) (δ : ℝ)
    (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hmem : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
      ‖κ * forecastLawDensityPhysicalTarget B U basis S law density selected sample xref
        active Y N gridVolume base physicalN τ o hb bW poly hmem u -
        ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (hmem : ∀ j d, coefficients (poly j) d ∈ U j)
    {P E Rrank M : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hX : (Fintype.card X : ℝ) ≤ P) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ P)
    (hLip : ((Lw * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hcoverF : ∀ i, ((Wtest.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp P)
    (hmodF : ∀ i, ((Wtest.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp P)
    (hmass : ∑ i, ‖c i‖ ≤ M)
    (hlarge : ∀ i, Real.exp ((max P E + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
    (hRrank : Real.exp ((max P E + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
      Rrank (U j) (poly j))
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D Pdecay δgrid : ℝ} (hD : 0 ≤ D)
    (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-Pdecay))
    (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
    (hmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
      forecastJointGridScale U basis R S.value physicalN τ j ≤ δgrid) :
    let frame := fixedSpatialKernelSliceFrame rootBudget rootLength z lowerG widthG
    let h0slice := fixedSpatialKernelBlock_slice_det_ne_zero e rootBudget rootLength z
      lowerG widthG false h0 hwGne
    let h1slice := fixedSpatialKernelBlock_slice_det_ne_zero e rootBudget rootLength z
      lowerG widthG true h1 hwGne
    let Cgrid := fixedSpatialOriginalForecastCap B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame true h1slice) hδP
    let Lgrid := fixedSpatialOriginalForecastLip B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame false h0slice)
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame true h1slice) hδP
    let Kgrid := Lw * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
    let grid := forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) xref
    let test := Wtest.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / physicalN a) τ
    ‖(𝔼 u ∈ integerBox physicalN, Wtest.eval physicalN poly u *
        (κ * forecastLawDensityPhysicalTarget B U basis S law density selected sample xref
          active Y N gridVolume base physicalN τ o hb bW poly hmem u)) -
      (∑' g, 𝔼 r : Out → ZMod N,
        ((rationalInactiveForecast law active grid Y N gridVolume g r / gridVolume : ℝ) : ℂ) *
          ∫ y, test g (fun a => ZMod.castHom hq (ZMod q) (r a)) y
            ∂realDensityMeasure volume density)‖ ≤
      (2 * δ + M * Real.exp (-E)) +
        forecastJointGridError (Fintype.card Out)
          (Fintype.card (X ⊕ AllocatedActiveIntegerAxis U basis S.value))
          (Fintype.card (Σ j, I j)) cutoff D Lgrid Cgrid Kgrid δgrid := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
