-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_spatial_witness_comparison
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocated_spatial_witness_comparison
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T00:52:06.200885+00:00
-- url     : https://prove2.me/theorems/f900fe9b-ebd7-4504-843a-1024094177f0
-- title:
--   Chart-event probability under the physical density matches the coefficient sampler law
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with decidable equality and finite types $E_j$ (all these types in the lowest universe), subspaces $U_j \le \mathbb R^{J_j}$, $\mathbb Z$-bases $bW_j$ indexed by $E_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (the integer lattice intersected with that subspace), bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)` such that ($h_b$) the $\mathbb Z$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`, orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$, reals $R_j, \sigma_j$, a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), and nonnegative reals $C_j, V_j$ such that the continuous linear equivalence $\chi_j =$ `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)` satisfies $\|\chi_j(v)\| \le C_j\|v\|$ and $0 \le$ `mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)` $\le V_j$ for all $j$. Write $\mathcal V$ for `LayerSamplerVariables G I n B` and $\Lambda_P$ for `allocatedFourierLogBudget m P`. Assume $R_j > 0$ and $0 < \sigma_j \le 1$; let $C^{\mathrm{inv}}_j \ge 0$ with $\|\chi_j^{-1}(v)\| \le C^{\mathrm{inv}}_j\|v\|$ and $C^{\mathrm{inv}}_j(|I_j|+1)R_j \le 1/4$; let $q > 0$ be a natural number; and let $P, \delta$ be reals with $0 \le P$, $m \le P$, $|\mathcal V| \le P$, $R_j^{-1}, \sigma_j^{-1} \le \exp P$, $|$`BoundedCoefficientExponent 𝒱 (j+1)`$| \le P$, $|I_j|, n_j, |J_j| \le P$ (all $j$), `probabilityProfileLipschitz` $\le \exp P$, $S.\mathrm{value} \le \exp P$, $C_j, V_j \le \exp P$, $q \le \exp P$, $\delta > 0$ and $\delta^{-1} \le \exp P$. Assume each lattice section is a $\mathbb Z$-lattice (`IsZLattice`) and the coefficient torus `CoefficientTorus U` (over $\mathcal V$) is compact with a Borel measurable structure; let $\mu$ be a translation-invariant probability measure on it and $\nu_j$ translation-invariant probability measures on the quotients of `euclideanSubspace (U j)` by the lattice sections. Let $X$ be a finite type with decidable equality, $\mathrm{poly}_j$ vector polynomials in variables $X$ over $\mathbb R$ with values in $\mathbb R^{J_j}$ of total degree at most $j+1$ with all coefficients in $U_j$ ($h_m$); reals $P_s, \varepsilon, \rho, R_s, S_{\max}$ with $0 \le P_s$, $|X| \le P_s$, $|\mathrm{Option}\,\mathcal V \times X| \le P_s$, $q \le \exp P_s$, $\varepsilon, \rho > 0$, $1/\varepsilon \le \exp P_s$, $1/\rho \le \exp P_s$; $\mathrm{stride} : X \to \mathbb N$ positive with $0 \le S_{\max} \le \exp P_s$ and $\mathrm{stride}(x)\,q \le S_{\max}$; $H : X \to \mathbb R$ with $\exp((P_s + c_m)^{c_m}) \le H(x)$, where $c_m =$ `allocatedMaskedTiltedConstant m` (a natural number chosen by OpenAI); `HasLayerSamplingRank (j+1) H Rs (U j) (poly j)` for all $j$, with $\exp((P_s + c_m)^{c_m}) \le R_s$; a nonempty finite set cells of `ColumnResiduePattern (Option 𝒱) X stride`; a predicate event on pairs (a map $\mathrm{Option}\,\mathcal V \times X \to \mathbb Z/q$, an element of `CoefficientChartResidues 𝒱 n E q`); $\mathrm{width} : \mathrm{Option}\,\mathcal V \times X \to \mathbb R$ positive with $\rho H(z_2) \le \mathrm{width}(z)$; $(4\Lambda_P + 2)^4 \le P_s$, $4\Lambda_P(4\Lambda_P+2)^4 + \Lambda_P \le P_s$; and $2\delta + \varepsilon \le 1/2$. For $z : \mathrm{Option}\,\mathcal V \times X \to \mathbb Z$ let $D(z) =$ `allocatedCoefficientDensity B U b hb o hR hσ S (affineSampleCoefficientTorus U poly hm z)` and $\mathrm{sample}(z) =$ `affineCoefficientCoverSample U poly hm q z` ($z$ cast to reals), and let $\mathfrak m =$ `selectedResidueDensityMass stride cells width D`. Then $D \ge 0$ pointwise, $0 < \sum'_z$ `selectedResidueSmoothWeight stride cells width z`, $0 < \mathfrak m$, $|\mathfrak m - 1| \le 2\delta + \varepsilon$, $1/2 \le \mathfrak m \le 3/2$, and
--   $$\Bigl|\textstyle\sum'_z \pi_D(z)\,\bigl[\texttt{coefficientDeckChartEvent}\ U\ bW\ b\ h_b\ o\ q\ (\mathrm{event}(z \bmod q))\ (\mathrm{sample}\ z)\bigr] - \sum'_z \pi(z) \int \bigl[\mathrm{event}(z \bmod q)(\texttt{coefficientSamplerChartResidues}\ q\ p_1\ p_2)\bigr]\,d(\mathrm{source} \otimes \mathrm{deck})(p)\Bigr| \le 12(2\delta + \varepsilon),$$
--   where $\pi_D$ is the probability mass function `selectedResidueDensityPMF stride cells width _ _ D _ _`, $\pi$ is `selectedResidueSmoothPMF stride cells width _ _`, $[\cdot]$ is $1$ or $0$, source is the measure `allocatedCoefficientSource B U b hR hσ S` on `CoefficientSamplerArrays I n` (over $\mathcal V$), and deck is the uniform probability measure on the finite type `CoefficientDeckResidues E q` (over $\mathcal V$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocated_spatial_witness_comparison` in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSpatialWitnessComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B050`, `OAIErdos3B161` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSpatialWitnessComparison.lean#L177

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B050
import Definitions.Def_OAIErdos3B161

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem exists_allocated_spatial_witness_comparison
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q] (hq : 0 < q)
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
    (event : ((Option (LayerSamplerVariables G I n B) × X) → ZMod q) →
      CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hsmallError : 2 * δ + ε ≤ 1 / 2) :
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 2 * δ + ε ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      |(∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
          (if coefficientDeckChartEvent U bW b hb o q (event (fun v => (z v : ZMod q))) (sample z) then 1 else 0)) -
        ∑' z, (selectedResidueSmoothPMF stride cells width hwidth hZ z).toReal *
          ∫ p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
              CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q,
            (if event (fun v => (z v : ZMod q)) (coefficientSamplerChartResidues q p.1 p.2) then (1 : ℝ) else 0)
            ∂(allocatedCoefficientSource B U b hR hσ S).prod
              (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).toMeasure| ≤
        12 * (2 * δ + ε) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
