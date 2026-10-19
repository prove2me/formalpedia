-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedUniformDegreeProductiveSource_s2
-- name    : OAI.Erdos3.VectorPolynomial.preparedUniformDegreeProductiveSource_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T08:18:05.618066+00:00
-- url     : https://prove2.me/theorems/834e9870-439f-44d0-a2ba-6706d65f986d
-- title:
--   Degree-zero prepared bounds and a witness scale give the productive source conclusion
-- statement:
--   All data are explicit binders of the theorem except the implicit naturals $m,n_X,M$, types $X_0,J_0$, reals $R_j,\sigma_j$, finite types $Q_j$ and reals $P_{\mathrm{seed}},Q_w,V_{\log},\mathrm{gainLog},\mathrm{gain}$. Let $\mathrm{prep}$ be a `RankPreparationFamily X₀ J₀ m` (layers with finite coordinate types $\mathrm{Coord}_j$); write $G$ for `EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))`, $B$ for `EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))` and $V$ for `LayerSamplerVariables G (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B`. Let $U_j\subseteq\mathbb{R}^{\mathrm{Coord}_j}$ be subspaces; $b_j$ bases of the orthogonal complement of `euclideanSubspace (U j)` indexed by $\mathrm{Fin}$(`preparedSamplerTransverse prep j`); $R_j>0$, $\sigma_j>0$ ($hR$, $h\sigma$); $S$ a `LayerSamplerScale` over $G,B,U,b,R,\sigma$; $\mathrm{stride},N:\mathrm{Fin}\,n_X\to\mathbb{N}$; $P_{\mathrm{detect}}\in\mathbb{N}[X]$; reals $p_{\mathrm{Model}},p_{\mathrm{Slice}}$; $V_{\mathrm{tail}}:\mathrm{Fin}\,m\to\mathbb{R}_{\ge0}$; reals $\tau,u,p,\mathrm{forecastCap}$; $hb$ (the $\mathbb{Z}$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`); orthonormal bases $o_j$ of `euclideanSubspace (U j)`; $\mathbb{Z}$-bases $bW_j$, indexed by $Q_j$, of `latticeSection (standardEuclideanLattice Coord_j) (euclideanSubspace (U j))`, each a $\mathbb{Z}$-lattice; a compact Borel structure on `CoefficientTorus U` over $V$ with a left-invariant probability measure $\mu$; left-invariant probability measures $\nu_j$ on the quotient tori; a compact Borel structure on `CoefficientTorus U` over $\mathrm{Fin}(0+1)$ with a left-invariant probability measure $\mu_{\mathrm{rows}}$; a Borel measurable structure on `SiteTorus (Finset (Fin (0 + 1))) U`; and reals $P_{\mathrm{chart}},P_{\mathrm{scale}},D,\mathrm{target},P_k,P_\rho,Q_{\mathrm{stride}},P_{\mathrm{master}},P_{\mathrm{late}},p_{\mathrm{Gain}},P_{\mathrm{physical}},\mathrm{coarseTarget},p_{\mathrm{Radius}}$. Write $u_{\mathrm{S}}=u+2p+1$ and $C$ = `sampledSupportedSlicedDetectionConstant 0 Pdetect`.
--
--   Assume: `PreparedUniformDegreeDirectScalarBounds m 0 nX |V| C Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius u_S pModel pSlice` (a conjunction of explicit inequalities); `PreparedUniformDegreeGeometryAt B U b S 0 C nX Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog u_S pModel) pRadius (2u_S + 4pModel + 7) pGain`; $R_j\le1$ and $R_j^{-1}\le e^{p_{\mathrm{Radius}}}$; $u,p\ge0$; $p_{\mathrm{Slice}}\,|V|\le p$; $4\prod_j$`earlyConstantDensityCap |PreparedSamplerContinuous prep j| (preparedSamplerTransverse prep j) (R j) (Vtail j)` $\le e^{p}$; $0\le\mathrm{forecastCap}\le e^{p}$; a natural number $Q_{\mathrm{good}}$; $m>0$, $n_X>0$, $|\mathrm{Coord}_j|\le M$; $p_{\mathrm{Radius}},P_{\mathrm{seed}},Q_w,V_{\log},\mathrm{gainLog}\ge0$; $1\le Q_{\mathrm{good}}\le e^{V_{\log}}$; `allocatedWitnessScaleLog Pseed Qw` $\le P_{\mathrm{late}}$; $e^{-\mathrm{gainLog}}\le\mathrm{gain}$; $0\le P_{\mathrm{chart}}$, $n_X\le P_{\mathrm{chart}}$, $\mathrm{gainLog}\le P_{\mathrm{chart}}$, $\mathrm{gainLog}+n_X+8\le P_{\mathrm{master}}$; $\tau=e^{-(\mathrm{gainLog}+n_X+8)}$; $S.\mathrm{value}\le\exp$(`allocatedWitnessScaleLog Pseed Qw`); and for all $j,i$ with $S.\mathrm{value}^{j+1}<$ `basisAxisScale (b j) i`,
--   $$8\cdot\text{probabilityProfileLipschitz}\cdot W\le\frac{\text{layerSamplerGapWidth}\ B\ R\ \langle j,i\rangle}{2}\cdot\frac{\text{basisAxisScale}(b_j,i)}{S.\mathrm{value}^{j+1}},$$
--   with $W$ = `physicalBadProductGap ((modularInitialBlockCount m (nX + m * M))(nX + m M)) (gainLog + 8) Vlog Qgood`. Then `PreparedUniformDegreeProductiveSourceConclusion` holds (a proposition defined by OpenAI) for $\mathrm{prep},U,b,S,hR,h\sigma,\mathrm{stride},N,P_{\mathrm{detect}},p_{\mathrm{Model}},p_{\mathrm{Slice}},V_{\mathrm{tail}},\tau,u,p,\mathrm{forecastCap},hb,o,bW,\mu$ and $P_{\mathrm{chart}},Q_{\mathrm{stride}},P_{\mathrm{master}},P_{\mathrm{late}},p_{\mathrm{Gain}},P_{\mathrm{physical}},\mathrm{coarseTarget},p_{\mathrm{Radius}},P_{\mathrm{scale}},P_{\mathrm{seed}},Q_w,\mathrm{gainLog},\mathrm{gain},V_{\log},Q_{\mathrm{good}}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedUniformDegreeProductiveSource_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.preparedUniformDegreeProductiveSource` (in `lean/OAI/Combinatorics/Progressions/Polynomial/PreparedUniformDegreeProductiveSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B290` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/PreparedUniformDegreeProductiveSource.lean (declaration OAI.Erdos3.VectorPolynomial.preparedUniformDegreeProductiveSource)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B290

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedUniformDegreeProductiveSource_s2
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [μ.IsAddLeftInvariant]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m 0 nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
      (sampledSupportedSlicedDetectionConstant 0 Pdetect)
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius (u + 2 * p + 1) pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt (m := m) («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) («I» := (PreparedSamplerContinuous prep)) («n» := (preparedSamplerTransverse prep)) («J» := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S 0
      (sampledSupportedSlicedDetectionConstant 0 Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog (u + 2 * p + 1) pModel) pRadius
      (2 * (u + 2 * p + 1) + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) ≤ p)
    (hCtail : (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j)) ≤ Real.exp p)
    (hForecastCap : 0 ≤ forecastCap) (hForecastCapP : forecastCap ≤ Real.exp p)
    {Pseed Qw Vlog gainLog gain : ℝ} (Qgood : ℕ)
    (hm : 0 < m) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hpRadius : 0 ≤ pRadius) (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw)
    (hVlog : 0 ≤ Vlog) (hg : 0 ≤ gainLog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hWitnessLate : allocatedWitnessScaleLog Pseed Qw ≤ Plate)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hchart : 0 ≤ Pchart) (hnChart : (nX : ℝ) ≤ Pchart)
    (hgChart : gainLog ≤ Pchart) (hGainMaster : gainLog + (nX : ℝ) + 8 ≤ Pmaster)
    (hτeq : τ = Real.exp (-(gainLog + (nX : ℝ) + 8)))
    (hS : (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M))
          (gainLog + 8) Vlog Qgood ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j, i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    PreparedUniformDegreeProductiveSourceConclusion
      (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (stride := stride) (N := N) (Pdetect := Pdetect) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (bW := bW) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius Pscale
      Pseed Qw gainLog gain Vlog Qgood := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
