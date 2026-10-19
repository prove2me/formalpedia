-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_spatial_residue_masked_comparison_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocated_spatial_residue_masked_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:49:10.544487+00:00
-- url     : https://prove2.me/theorems/2ee2beca-dd20-4b51-a20c-93cee1b96460
-- title:
--   Selected-residue sampling of the allocated coefficient density has mass near one and compares masked density ratios with masked torus integrals
-- statement:
--   All named objects below are defined by OpenAI. Let $m$ be a natural number, $G$ a finite type, and for $j < m$ let $I_j$, $J_j$ be finite types and $n_j$ natural numbers; let $B_a$ be finite types indexed by `LayerSamplerAxis I n`. For each $j$ let $U_j$ be a real subspace of $\mathbb{R}^{J_j}$ and $b_j$ a basis, indexed by $\{0,\dots,n_j-1\}$, of the orthogonal complement of the Euclidean copy of $U_j$; let `hb` be a proof that for each $j$ the $\mathbb{Z}$-span of the range of $b_j$ is the `projectedIntegerLattice` of the Euclidean copy of $U_j$; let $o_j$ be an orthonormal basis (indexed by $I_j$) of the Euclidean copy of $U_j$. Let $R_j, \sigma_j$ be reals and $S$ a `LayerSamplerScale B U b R σ` (scale value `S.value`). Write $K$ for `LayerSamplerVariables G I n B` and $\Phi_j$ for `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)`, the linear isomorphism of $\mathbb{R}^{J_j}$ (Euclidean) with $U_j \times \mathbb{R}^{n_j}$ given by orthogonal projection to $U_j$ and the $b_j$-coordinates of the projection to $U_j^\perp$, each divided by `basisAxisScale (b j) i`.
--
--   Let $C_j, V_j$ be nonnegative reals with $\|\Phi_j(x)\| \le C_j\|x\|$ for all $j, x$, and $0 \le$ `mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)` $\le V_j$ for all $j$ (this ratio is the covolume of the lattice section of $\mathbb{Z}^{J_j}$ in $U_j$ divided by $\prod_i$ `basisAxisScale (b j) i`). Assume further:
--   - $R_j > 0$, $\sigma_j > 0$, $\sigma_j \le 1$ for all $j$;
--   - $C^{\mathrm{inv}}_j \ge 0$ are reals with $\|\Phi_j^{-1}(v)\| \le C^{\mathrm{inv}}_j\|v\|$ for all $j, v$, and $C^{\mathrm{inv}}_j\,(|I_j|+1)\,R_j \le 1/4$ for all $j$;
--   - $q$ is a natural number with $q > 0$; $P, \delta$ are reals with $0 \le P$, $m \le P$, $|K| \le P$, and for all $j$: $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$, $|\texttt{BoundedCoefficientExponent}\ K\ (j+1)| \le P$, $|I_j| \le P$, $n_j \le P$, $|J_j| \le P$, $C_j \le e^P$, $V_j \le e^P$; also `probabilityProfileLipschitz` $\le e^P$, $\mathrm{S.value} \le e^P$, $q \le e^P$, $\delta > 0$ and $\delta^{-1} \le e^P$;
--   - each lattice section of $\mathbb{Z}^{J_j}$ in $U_j$ is a full-rank $\mathbb{Z}$-lattice; the `CoefficientTorus` (over $K$, for $U$) is compact, carries its Borel $\sigma$-algebra, and $\mu$ is an additively left-invariant probability measure on it; $\nu_j$ are additively left-invariant probability measures on the quotients of the Euclidean copies of $U_j$ by the lattice sections;
--   - $X$ is a finite type with decidable equality and `poly j` are vector polynomials in the variables $X$ with values in $\mathbb{R}^{J_j}$, of degree at most $j+1$ (`DegreeLE` with weights $1$), with all coefficients in $U_j$ (proof `hm`);
--   - $P_s, \varepsilon, \rho, R_s, S_{\max}$ are reals with $0 \le P_s$, $|X| \le P_s$, $|\texttt{Option}\ K \times X| \le P_s$, $q \le e^{P_s}$, $\varepsilon > 0$, $\rho > 0$, $1/\varepsilon \le e^{P_s}$, $1/\rho \le e^{P_s}$;
--   - `stride : X → ℕ` is positive everywhere; $0 \le S_{\max} \le e^{P_s}$ and $\mathrm{stride}(x)\,q \le S_{\max}$ for all $x$;
--   - $H : X \to \mathbb{R}$ with $\exp((P_s + c_m)^{c_m}) \le H(x)$ for all $x$, where $c_m$ = `allocatedMaskedTiltedConstant m`; for each $j$, `HasLayerSamplingRank (j+1) H Rs (U j) (poly j)` (for every nonzero-on-$U_j$ integer vector $a$ with entries of absolute value at most $R_s$, the degree-$(j+1)$ homogeneous part of the integer row polynomial $a \cdot \mathrm{poly}_j$ admits no `PolynomialRationalApproximation H Rs`); and $\exp((P_s + c_m)^{c_m}) \le R_s$;
--   - `cells` is a nonempty finite set of `ColumnResiduePattern (Option K) X stride` (residue patterns assigning to each $(k, x)$ a residue modulo $\mathrm{stride}(x)$);
--   - `mask r z` $\in [0,1]$ for all residue arrays $r : \texttt{Option}\ K \times X \to \mathbb{Z}/q$ and $z$ : `CoefficientAmbientIndex K J` $\to \mathbb{Z}/q$;
--   - `width : Option K × X → ℝ` with `width z` $> 0$ and $\rho\,H(z_2) \le$ `width z` for all $z$;
--   - with $F$ = `allocatedFourierLogBudget m P`: $(4F+2)^4 \le P_s$ and $4F(4F+2)^4 + F \le P_s$;
--   - $2\delta + \varepsilon \le 1/2$.
--
--   Define $D$ = `allocatedCoefficientDensity B U b hb o hR hσ S` (a density on the coefficient torus), $D_c(x) = D(\texttt{quotientIntegerCover (coefficientIntegerLattice U) q}\ x)$, $A_r$ = `allocatedMaskedCoefficientDensity B U b o S q (mask r)`, and for an integer array $z : \texttt{Option}\ K \times X \to \mathbb{Z}$: $\mathrm{sample}(z)$ = `affineCoefficientCoverSample U poly hm q` $(k, x \mapsto z(k,x))$ (the affine sample coefficient array scaled by $1/q$, reduced modulo the coefficient lattice) and $D_{\mathrm{phys}}(z) = D(\texttt{affineSampleCoefficientTorus U poly hm}\ (k,x \mapsto z(k,x)))$.
--
--   Then $D_{\mathrm{phys}}(z) \ge 0$ for all $z$; the total weight $Z = \sum_z w(z)$ is positive, where $w$ = `selectedResidueSmoothWeight stride cells width` ($w(z)$ is OpenAI's smooth product profile at $z/\mathrm{width}$ if the column residue pattern of $z$ lies in `cells`, and $0$ otherwise); and $\mathcal{M}$ = `selectedResidueDensityMass stride cells width D_phys` (the finite density mass of $D_{\mathrm{phys}}$ under the weights $w$) is positive. Moreover $|\mathcal{M} - 1| \le 2\delta + \varepsilon$, $1/2 \le \mathcal{M} \le 3/2$, and
--   $$\Bigl|\sum_z \pi_D(z)\,\frac{A_{\bar z}(\mathrm{sample}(z))}{D_c(\mathrm{sample}(z))} - \sum_z \pi(z) \int A_{\bar z}\,d\mu\Bigr| \le 12\,(2\delta + \varepsilon),$$
--   where $\bar z$ is $z$ reduced modulo $q$, $\pi_D$ = `selectedResidueDensityPMF stride cells width hwidth hZ D_phys hD0 hDpos` (the $D_{\mathrm{phys}}$-tilted PMF), $\pi$ = `selectedResidueSmoothPMF stride cells width hwidth hZ` (the PMF proportional to $w$), and the ratio is `dominatedDensityRatio`, $A/D$ computed in $\mathbb{R}$ (with Lean's convention $a/0 = 0$) and cast to $\mathbb{C}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocated_spatial_residue_masked_comparison_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_allocated_spatial_residue_masked_comparison` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSpatialResidueMaskedComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B176` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSpatialResidueMaskedComparison.lean (declaration OAI.Erdos3.VectorPolynomial.exists_allocated_spatial_residue_masked_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B176

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in

theorem exists_allocated_spatial_residue_masked_comparison_s2
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) (hq : 0 < q)
    {P δ : ℝ} (hP : 0 ≤ P) (hmP : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hqP : (q : ℝ) ≤ Real.exp P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type} [Fintype X] [DecidableEq X]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {Ps ε ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hqPs : (q : ℝ) ≤ Real.exp Ps)
    (hε : 0 < ε) (hρ : 0 < ρ) (hεPs : 1 / ε ≤ Real.exp Ps) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, ((stride x * q : ℕ) : ℝ) ≤ Smax)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hcells : cells.Nonempty)
    (mask : ((Option (LayerSamplerVariables G I n B) × X) → ZMod q) →
      (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (hmask : ∀ r z, mask r z ∈ Set.Icc (0 : ℝ) 1)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hsmallError : 2 * δ + ε ≤ 1 / 2) :
    let D := allocatedCoefficientDensity B U b hb o hR hσ S
    let Dc := fun x => D (quotientIntegerCover (coefficientIntegerLattice U) q x)
    let A := fun r => allocatedMaskedCoefficientDensity B U b o S q (mask r)
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ => D (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 2 * δ + ε ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      ‖(∑' z, ((selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal : ℂ) *
          dominatedDensityRatio Dc (A (fun v => (z v : ZMod q))) (sample z)) -
        ∑' z, ((selectedResidueSmoothPMF stride cells width hwidth hZ z).toReal : ℂ) *
          ((∫ x, A (fun v => (z v : ZMod q)) x ∂μ) : ℂ)‖ ≤ 12 * (2 * δ + ε) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
