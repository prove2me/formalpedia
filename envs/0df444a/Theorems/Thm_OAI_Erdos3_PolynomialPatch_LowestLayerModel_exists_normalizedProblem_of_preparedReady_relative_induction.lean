-- Prove2me | Theorems.Thm_OAI_Erdos3_PolynomialPatch_LowestLayerModel_exists_normalizedProblem_of_preparedReady_relative_induction
-- name    : OAI.Erdos3.PolynomialPatch.LowestLayerModel.exists_normalizedProblem_of_preparedReady_relative_induction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:23:06.779522+00:00
-- url     : https://prove2.me/theorems/39d8abad-2553-4d36-94e5-7aec49c8662b
-- title:
--   A ready prepared center upgrades to normalized candidate problems for a lowest-layer patch
-- statement:
--   Fix natural numbers $m,q,s,D,E,n_X,M_{\mathrm{slot}}$ with $m\le q$, and a `RankPreparationFamily (Fin nX) (Fin D) m` $L$ (a family of $m$ rank-preparation layers); `L.pad q` is the family of $q$ layers that agrees with $L$ below $m$ and is empty above. Write $G$ for `EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))` (a finite type $\mathrm{Fin}\,k$ for an explicit $k$), $B$ for the block types `EnlargedPreparedCommonSamplerBlock (L.pad q) …`, and $V$ for the finite type `LayerSamplerVariables G (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) B`. The section data used are: finite types $\mathrm{Deck}_j$ ($j<q$); subspaces $U_j$ of $\mathbb{R}^{\mathrm{Coord}_j}$, where $\mathrm{Coord}_j$ is the coordinate type of the $j$-th padded layer; bases $b_j$ of the orthogonal complement of `euclideanSubspace (U j)`; the hypothesis $hb$ that the $\mathbb{Z}$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`; orthonormal bases $o_j$ of `euclideanSubspace (U j)`; reals $R_j,\sigma_j$ with $R_j>0$, $\sigma_j>0$ ($hR$, $h\sigma$); a `LayerSamplerScale` $S$ for this data; $\mathbb{Z}$-bases $bW_j$, indexed by $\mathrm{Deck}_j$, of the lattice `latticeSection (standardEuclideanLattice Coord_j) (euclideanSubspace (U j))` (assumed a $\mathbb{Z}$-lattice); and a measure $\mu$ on `CoefficientTorus U` over $V$ (with a measurable structure).
--
--   The theorem then takes: a `PolynomialPatch (Fin nX) s (D + E)` named $\mathrm{oldPatch}$ and a `oldPatch.LowestLayerModel m` named $F$ (a structure bundling a strictly lower-triangular $D\times D$ real matrix and origin polynomials of degree at most $m$ describing the first $D$ slots, whose weights equal $m$); integer polynomials $ip_i$ ($i<D$) of total degree at most $m$, $c_0\in\mathbb{R}^D$ and a vector polynomial $\mathrm{err}$ with $\mathrm{ofCoordinates}(F.\mathrm{normalizedOrigin})=L.\mathrm{polynomial}+$ `integerCoordinates ip` $+\,1\otimes c_0+\mathrm{err}$; every coefficient of the $j$-th padded polynomial lies in $U_j$ and it has degree at most $j+1$; $\sigma_j\le1$; $C_j\ge0$ bounding the inverse `normalizedOrthogonalChart` of $b_j$ ($\|\cdot^{-1}v\|\le C_j\|v\|$); $N:\mathrm{Fin}\,n_X\to\mathbb{N}$ and reals $\tau\le1/2$, $\xi\le1$ with $4\le\tau N_x$ for all $x$; $\mathrm{stride}:\mathrm{Fin}\,n_X\to\mathbb{N}$; a finset $\mathrm{cells}$ of `ColumnResiduePattern`s; $A_{\mathrm{candidate}}$, an `AllocatedExternalCandidateSamplerFamily` for this data (an `AllocatedExternalCandidateSampler` at every center of the coefficient torus); reals $\delta\ge0$ and $0<\mathrm{gain}\le1$ with $|\mathrm{err}(x)_i|\le\delta$ for $x$ in `integerBox N`; reals $p\ge0$ and $P_{\mathrm{early}}$ with $D,q,\mathrm{oldPatch.kernel.lip},|\mathrm{Coord}_j|,C_j\le e^{p}$, $e^{-p}\le\mathrm{gain}$, $\delta\le e^{-(3p+130)}$, $6p+35\le P_{\mathrm{early}}$, and $C'_j(|\mathrm{PreparedSamplerContinuous}_j|+1)R_j\le1/4$ for all $j$ and every $C'\ge0$ with $C'_j\le e^{P_{\mathrm{early}}}$; natural numbers $n_0,\mathrm{stage},d_0$, a real $\mathrm{discount}$ and functions $\mathrm{cutoff},\mathrm{childCost}:\mathbb{R}\to\mathbb{R}$ with `RelativePatchInductionRule s n₀ stage discount cutoff childCost`; reals $p_{\mathrm{child}},a,\Lambda$ with $2\le p$, $p+2\le p_{\mathrm{child}}$, $e^{-p}\le a\le\Lambda\le1$, and `RelativePatchAbsoluteRule s n₀ p a Λ d₀`; $|V|\le p_{\mathrm{child}}$; a natural number $H\le S.\mathrm{value}$ with $e^{\mathrm{cutoff}(p_{\mathrm{child}})}\le H$; $D>0$; $m<\mathrm{oldPatch.weight}(D+i)$ for all $i<E$; `relativePatchComplexity oldPatch` ($=(D+E)+\log(1+\mathrm{lip})$) $\le p_{\mathrm{child}}$; `relativePatchDistinctWeights oldPatch` (number of distinct weights) $\le\mathrm{stage}+1$; $f:\mathbb{Z}^{n_X}\to\mathbb{R}$ with values in $[0,1]$ on `integerBox N` and whose support in the box is free of $(s+2)$-term progressions (`IntegerVectorAPFree`); $\mathrm{discount}\in[0,1]$; $\mathrm{childCost}(p_{\mathrm{child}})\ge0$; a real $\mathrm{initialCost}\ge\mathrm{childCost}(p_{\mathrm{child}})$ with $H\le e^{\mathrm{initialCost}}$; a real $\mathrm{gainLog}$, a natural number $Q_{\mathrm{good}}$, an embedding $e_{\mathrm{Ready}}:\mathrm{Fin}\,2\times\mathrm{Fin}\,n_X\hookrightarrow G$, and a predicate $\mathrm{Ready}$ on the coefficient torus; and finally `PreparedCenteredProductiveGoodCenterReadyConclusion` for this data with widths `allocatedExternalCandidateWidths … N τ ξ`, bases `(Acandidate 0).bases`, law `Acandidate.law`, and test `relativePatchSourceTest N f a oldPatch` ($y\mapsto(\text{relative box input at }\lfloor y\rfloor-a)\cdot\mathrm{oldPatch.value}(y)$).
--
--   Conclusion: `PreparedCenteredProductiveGoodCenterEnhancedConclusion` holds for the same data, with the extra predicate sending $(\mathrm{center},\mathrm{centerLift},\mathrm{productive})$ to `AllocatedNormalizedCandidateConclusion` for the sampler `Acandidate center`, with keep-predicate $k\mapsto H\le(\text{Acandidate center}).\mathrm{sides}\,k$, child cost $\mathrm{childCost}(p_{\mathrm{child}})$, cost $\mathrm{initialCost}$, rank bound $d_0+sE$, function $f$ and target $(1-\mathrm{discount})^{\mathrm{stage}+1}\Lambda$ (this predicate asserts the existence of a polynomial patch of bounded size and an `AllocatedExternalCandidateProblem` on its shear nilmanifold with productive set inside $\mathrm{productive}$ and the given center lift and keep-predicate).
--
--   Lean: `OAI.Erdos3.PolynomialPatch.LowestLayerModel.exists_normalizedProblem_of_preparedReady_relative_induction` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedReadyPaddedRelativeInitialization.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1331`, `OAIErdos3B1348` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedReadyPaddedRelativeInitialization.lean#L285

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1331
import Definitions.Def_OAIErdos3B1348

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators TensorProduct Classical

variable {m q s D E nX Mslot : ℕ}
variable (L : RankPreparationFamily (Fin nX) (Fin D) m) (hmq : m ≤ q)
variable {Deck : Fin q → Type} [∀ j, Fintype (Deck j)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin ((preparedSamplerTransverse (L.pad q)) j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous (L.pad q)) j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot)))) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))) U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (L.pad q j).Coord) (euclideanSubspace (U j)))]

variable (bW : ∀ j, Basis (Deck j) ℤ
  (latticeSection (standardEuclideanLattice (L.pad q j).Coord) (euclideanSubspace (U j))))
variable [MeasurableSpace (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))))) U)]
variable (μ : Measure (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))))) U))

include hmq in
theorem exists_normalizedProblem_of_preparedReady_relative_induction
    {oldPatch : PolynomialPatch (Fin nX) s (D + E)} (F : oldPatch.LowestLayerModel m)
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (N : Fin nX → ℕ) {τ ξ : ℝ} (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (stride : Fin nX → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))))) (Fin nX) stride))
    (Acandidate : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))) U b S hb o hR hσ N
      (fun j => (L.pad q j).poly) hm τ ξ stride cells)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain) (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (oldPatch.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card ((PreparedSamplerContinuous (L.pad q)) j) : ℝ) + 1) * R j ≤ 1 / 4)
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff childCost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p + 2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot)))) : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < oldPatch.weight (i.natAdd D))
    (hA : relativePatchComplexity oldPatch ≤ pchild)
    (hstage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost pchild) (initialCost : ℝ)
    (hCost : childCost pchild ≤ initialCost) (hHcost : (H : ℝ) ≤ Real.exp initialCost)
    (gainLog : ℝ) (Qgood : ℕ) (eReady : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))))
    (Ready : CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))))) U → Prop)
    (hready : PreparedCenteredProductiveGoodCenterReadyConclusion
      (m := q) (nX := nX) (M := Mslot) (L.pad q) U b S bW hb o hR hσ μ
      (fun j => (L.pad q j).poly) hm stride
      (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))) U b S N τ ξ) (Acandidate 0).bases
      gainLog gain Qgood eReady Acandidate.law N (relativePatchSourceTest N f a oldPatch) Ready) :
    PreparedCenteredProductiveGoodCenterEnhancedConclusion
      (m := q) (nX := nX) (M := Mslot) (L.pad q) U b S bW hb o hR hσ μ
      (fun j => (L.pad q j).poly) hm stride
      (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))) U b S N τ ξ) (Acandidate 0).bases
      gainLog gain Qgood eReady Acandidate.law N (relativePatchSourceTest N f a oldPatch) Ready
      (fun center centerLift productive =>
        AllocatedNormalizedCandidateConclusion (E := Deck) (A := Acandidate center)
          s (fun k => H ≤ (Acandidate center).sides k) centerLift productive
          (childCost pchild) initialCost (d₀ + s * E) f ((1 - discount) ^ (stage + 1) * Λ)) := by
  sorry

end Erdos3.PolynomialPatch.LowestLayerModel
end
end OAI
