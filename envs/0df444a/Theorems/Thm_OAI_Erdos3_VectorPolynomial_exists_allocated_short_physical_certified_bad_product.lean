-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_short_physical_certified_bad_product
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocated_short_physical_certified_bad_product
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T01:16:07.100858+00:00
-- url     : https://prove2.me/theorems/9b592225-cfae-4573-a870-c1c82d0f1abe
-- title:
--   A certified read map makes large bad prime-power products rare under the physical law
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with decidable equality and finite types $E_j$ (all these types in the lowest universe), subspaces $U_j \le \mathbb R^{J_j}$, $\mathbb Z$-bases $bW_j$ indexed by $E_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (the integer lattice intersected with that subspace), bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)` such that ($h_b$) the $\mathbb Z$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`, orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$, reals $R_j, \sigma_j$, a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), and nonnegative reals $C_j, V_j$ such that the continuous linear equivalence $\chi_j =$ `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)` satisfies $\|\chi_j(v)\| \le C_j\|v\|$ and $0 \le$ `mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)` $\le V_j$ for all $j$. Let $E_{\log}, V_{\log}$ be reals and $Q \in \mathbb N$; put $\kappa =$ `physicalBadProductAccuracy Elog Vlog` $= e^{-(V_{\log} + 3E_{\log} + 16)}$, $R_{\mathrm{bad}} =$ `quantitativeBadPrimeRadius Elog` $= \lceil 4e^{E_{\log}} \rceil + 1$, $\mathrm{cap} = \max(Q, R_{\mathrm{bad}}^2)$, and let inactive be the predicate `allocatedShortAxis U b S.value` on `LayerSamplerAxis I n`. Write $\mathcal V$ for `LayerSamplerVariables G I n B`, $\Lambda_P$ for `allocatedFourierLogBudget m P` and $\lambda$ for the constant `probabilityProfileLipschitz`. Assume $E_{\log}, V_{\log} \ge 0$, $1 \le Q \le \exp V_{\log}$, $0 < m$, $R_j > 0$, $0 < \sigma_j \le 1$; let $C^{\mathrm{inv}}_j \ge 0$ with $\|\chi_j^{-1}(v)\| \le C^{\mathrm{inv}}_j\|v\|$ and $C^{\mathrm{inv}}_j(|I_j|+1)R_j \le 1/4$; let $P$ be a real with $0 \le P$, $m \le P$, $|\mathcal V| \le P$, $R_j^{-1}, \sigma_j^{-1} \le \exp P$, $|$`BoundedCoefficientExponent 𝒱 (j+1)`$| \le P$, $|I_j|, n_j, |J_j| \le P$ (all $j$), $\lambda \le \exp P$, $S.\mathrm{value} \le \exp P$, $C_j, V_j \le \exp P$, and $V_{\log} + 3E_{\log} + 16 \le P$. Assume each lattice section is a $\mathbb Z$-lattice (`IsZLattice`) and the coefficient torus `CoefficientTorus U` (over $\mathcal V$) is compact with a Borel measurable structure; let $\mu$ be a translation-invariant probability measure on it and $\nu_j$ translation-invariant probability measures on the quotients of `euclideanSubspace (U j)` by the lattice sections. Let $X$ be a finite type with decidable equality, $\mathrm{poly}_j$ vector polynomials in variables $X$ over $\mathbb R$ with values in $\mathbb R^{J_j}$ of total degree at most $j+1$ with all coefficients in $U_j$ ($h_m$); reals $P_s, \rho, R_s, S_{\max}$ with $0 \le P_s$, $|X| \le P_s$, $|\mathrm{Option}\,\mathcal V \times X| \le P_s$, $V_{\log} + 3E_{\log} + 16 \le P_s$, $\rho > 0$, $1/\rho \le \exp P_s$; $\mathrm{stride} : X \to \mathbb N$ positive with $0 \le S_{\max} \le \exp P_s$ and $\mathrm{stride}(x)\,\mathrm{cap} \le S_{\max}$; $H : X \to \mathbb R$ with $\exp((P_s + c_m)^{c_m}) \le H(x)$, where $c_m =$ `allocatedMaskedTiltedConstant m` (a natural number chosen by OpenAI); `HasLayerSamplingRank (j+1) H Rs (U j) (poly j)` for all $j$, with $\exp((P_s + c_m)^{c_m}) \le R_s$; a nonempty finite set cells of `ColumnResiduePattern (Option 𝒱) X stride`; $L, D \in \mathbb N$, embeddings $\mathrm{spatial} : \mathrm{Fin}\,L \hookrightarrow G$, $\mathrm{kernel}_j : \mathrm{Fin}\,L \times \mathrm{Fin}(j+1) \hookrightarrow G$, $\mathrm{block}_{j,a} : \mathrm{Fin}\,L \hookrightarrow B_{(j,a)}$ for $a \in$ `AllocatedDegreeActiveAxis inactive j`; a real rankC $\ge 0$ with $|X| + \sum_j (|E_j| + n_j) \le D$ and $\lceil 2(\mathrm{rankC} + D + 10)/$`modularRankSmallBallExponent m`$\rceil \le L$ (where `modularRankSmallBallExponent m` $= 2^{1-m}$); $\mathrm{width} : \mathrm{Option}\,\mathcal V \times X \to \mathbb R$ positive with $\rho H(z_2) \le \mathrm{width}(z)$; $(4\Lambda_P + 2)^4 \le P_s$ and $4\Lambda_P(4\Lambda_P+2)^4 + \Lambda_P \le P_s$; $8\lambda \le$ `residueProfileWidth stride width z` for all $z$; and, with $w_j =$ `allocatedShortRankSelectedWidth B U b S spatial stride width j`, $8\lambda\,\mathrm{cap} \le w_j$ for all $j$ and $\sum_j 16\lambda\,\mathrm{cap}/w_j \le \kappa$. Let $D_{\mathrm{ph}}(z) =$ `allocatedCoefficientDensity B U b hb o hR hσ S (affineSampleCoefficientTorus U poly hm z)` for $z : \mathrm{Option}\,\mathcal V \times X \to \mathbb Z$ (cast to reals), and $\mathfrak m =$ `selectedResidueDensityMass stride cells width D_ph`. Then $D_{\mathrm{ph}} \ge 0$ pointwise, $0 < \sum'_z$ `selectedResidueSmoothWeight stride cells width z`, $0 < \mathfrak m$, and there is $\mathrm{read}$ from $\mathrm{Option}\,\mathcal V \times X \to \mathbb Z$ to integer arrays on `AllocatedActualCoefficientIndex G X I E n B` such that: (1) `allocatedReadNoise (read z) = z` for all $z$; (2) for every $z$ with $D_{\mathrm{ph}}(z) \ne 0$, every finite set primes of nonzero natural numbers, every $\mathrm{depth} : \mathbb N \to \mathbb N$ and every $q > 0$ with $p^{\mathrm{depth}(p)} \mid q$ for all $p \in$ primes, `coefficientDeckChartEvent U bW b hb o q (allocatedChartResiduePrimePowerWitness inactive rankC primes depth q _ (z mod q)) (affineCoefficientCoverSample U poly hm q z)` holds if and only if `allocatedActualModulusBad inactive spatial kernel block rankC (p^depth(p)) (read z)` holds for every $p \in$ primes; (3) $|\mathfrak m - 1| \le 3\kappa$ and $1/2 \le \mathfrak m \le 3/2$; (4) $0 < R_{\mathrm{bad}} \le \exp(E_{\log} + 3)$; and (5) for every finite set primes of primes and every $\mathrm{depth} : \mathbb N \to \mathbb N$ with $p^{\mathrm{depth}(p)} \le Q$ for all $p \in$ primes,
--   $$\textstyle\sum'_z \pi_D(z)\,\Bigl[\bigl(\prod_x \mathrm{stride}(x)\bigr)^2 \cdot \texttt{smallPrimePowerCorrection}(\texttt{modularCoefficientPrimeThreshold}\ m) \cdot R_{\mathrm{bad}} < \prod_{p \in \mathrm{primes}} p^{a_p(z)}\Bigr] \le e^{-E_{\log}},$$
--   where $\pi_D$ is the probability mass function `selectedResidueDensityPMF stride cells width _ _ D_ph _ _`, $[\cdot]$ is $1$ or $0$, and $a_p(z) =$ `largestTestedBadDepth depth (p a z ↦ allocatedActualPrimeBad inactive spatial kernel block primes rankC p a (read z)) p z` (the largest $a \in [1, \mathrm{depth}(p)]$ for which that predicate holds, or $0$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocated_short_physical_certified_bad_product` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedCertifiedPhysicalBadProduct.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B050`, `OAIErdos3B147`, `OAIErdos3B161` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedCertifiedPhysicalBadProduct.lean#L288

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B050
import Definitions.Def_OAIErdos3B147
import Definitions.Def_OAIErdos3B161

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

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

variable (Elog Vlog : ℝ) (Q : ℕ)
local notation "κ" => physicalBadProductAccuracy Elog Vlog
local notation "Rbad" => quantitativeBadPrimeRadius Elog
local notation "cap" => (max Q (Rbad ^ 2) : ℕ)
local notation "inactive" => allocatedGridAxis (I := I) U b S.value

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

variable (Elog Vlog : ℝ) (Q : ℕ)
local notation "κ" => physicalBadProductAccuracy Elog Vlog
local notation "Rbad" => quantitativeBadPrimeRadius Elog
local notation "cap" => (max Q (Rbad ^ 2) : ℕ)
local notation "inactive" => allocatedShortAxis (I := I) U b S.value

include bW hC hV in
theorem exists_allocated_short_physical_certified_bad_product
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    {P : ℝ} (hP : 0 ≤ P) (hmP : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hbudgetP : Vlog + 3 * Elog + 16 ≤ P)
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
    {Ps ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hbudgetPs : Vlog + 3 * Elog + 16 ≤ Ps)
    (hρ : 0 < ρ) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, ((stride x * cap : ℕ) : ℝ) ≤ Smax)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hcells : cells.Nonempty)
    {L D : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (rankC : ℝ) (hrankC : 0 ≤ rankC)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    (hL : ⌈2 * (rankC + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride width z)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * (cap : ℝ) ≤
      allocatedShortRankSelectedWidth B U b S spatial stride width j)
    (hresidueError : (∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (cap : ℝ) /
      allocatedShortRankSelectedWidth B U b S spatial stride width j) ≤ κ) :
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
    ∃ read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ,
      (∀ z, allocatedReadNoise (read z) = z) ∧
      (∀ z, Dphysical z ≠ 0 →
        ∀ (primes : Finset ℕ) (hne : ∀ p : primes, NeZero p.val),
          letI := hne
          ∀ (depth : ℕ → ℕ) (q : ℕ) (hq : 0 < q),
            letI : NeZero q := ⟨hq.ne'⟩
            ∀ hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q,
              coefficientDeckChartEvent U bW b hb o q
                (allocatedChartResiduePrimePowerWitness inactive rankC primes depth q hdiv
                  (fun v => (z v : ZMod q)))
                (affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))) ↔
              ∀ p : primes, allocatedActualModulusBad inactive spatial kernel block rankC
                (p.val ^ depth p.val) (read z)) ∧
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 3 * κ ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      0 < Rbad ∧ (Rbad : ℝ) ≤ Real.exp (Elog + 3) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
          (∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
            (if (∏ x, stride x) ^ 2 *
              (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * Rbad) <
                ∏ p ∈ primes, p ^ largestTestedBadDepth depth
                  (fun p a z => allocatedActualPrimeBad inactive spatial kernel block primes rankC p a (read z)) p z
              then (1 : ℝ) else 0)) ≤ Real.exp (-Elog) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
