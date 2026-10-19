-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_sharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface_of_goodModel_s2
-- name    : OAI.Erdos3.VectorPolynomial.sharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface_of_goodModel_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T08:31:07.345639+00:00
-- url     : https://prove2.me/theorems/30134d50-a40e-442c-961a-1b11ecabfd2d
-- title:
--   Productive bounds upgrade the good-model interface to the productive good-model interface
-- statement:
--   All data are explicit binders of the theorem except the implicit naturals $m,n_X,M$, types $X_0,J_0$, reals $R_j,\sigma_j$, finite types $Q_j$ and a real $D$. Let $\mathrm{prep}$ be a `RankPreparationFamily X₀ J₀ m` (layers with finite coordinate types $\mathrm{Coord}_j$); write $G$ for `EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))`, $B$ for `EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))` and $V$ for `LayerSamplerVariables G (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B`. Let $U_j\subseteq\mathbb{R}^{\mathrm{Coord}_j}$ be subspaces; $b_j$ bases of the orthogonal complement of `euclideanSubspace (U j)` indexed by $\mathrm{Fin}$(`preparedSamplerTransverse prep j`); $R_j>0$, $\sigma_j>0$ ($hR$, $h\sigma$); $S$ a `LayerSamplerScale` over $G,B,U,b,R,\sigma$; $\mathrm{selection}:\mathrm{Fin}(0+1)\hookrightarrow G$; $\mathrm{stride},N:\mathrm{Fin}\,n_X\to\mathbb{N}$; $P_{\mathrm{detect}}\in\mathbb{N}[X]$; reals $u_{\mathrm{Source}},p_{\mathrm{Model}},p_{\mathrm{Slice}}$; $V_{\mathrm{tail}}:\mathrm{Fin}\,m\to\mathbb{R}_{\ge0}$; reals $\tau,u,p,\mathrm{forecastCap}$; $hb$ (the $\mathbb{Z}$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`); orthonormal bases $o_j$ of `euclideanSubspace (U j)`; $\mathbb{Z}$-bases $bW_j$, indexed by $Q_j$, of `latticeSection (standardEuclideanLattice Coord_j) (euclideanSubspace (U j))`, each a $\mathbb{Z}$-lattice; a compact Borel structure on `CoefficientTorus U` over $V$ with a left-invariant probability measure $\mu$; left-invariant probability measures $\nu_j$ on the quotient tori; reals $P_{\mathrm{chart}},Q_{\mathrm{stride}},P_{\mathrm{master}},P_{\mathrm{late}},p_{\mathrm{Gain}},P_{\mathrm{physical}},\mathrm{coarseTarget},B_0,\mathrm{gainLog},\mathrm{gain},P_{\mathrm{good}}$; a natural number $Q_{\mathrm{good}}$; an embedding $\mathrm{spatialEmbedding}:\mathrm{Fin}\,2\times\mathrm{Fin}\,n_X\hookrightarrow G$; and a real $P_{\mathrm{prod}}$. Assume `PreparedCenteredForecastProductiveBounds prep U b S selection Pdetect uSource pModel pSlice Vtail τ u p forecastCap Pchart Qstride Pmaster Plate Pphysical coarseTarget gainLog Pprod D` (a structure of hypotheses defined by OpenAI: $n_X>0$, $\sigma_j\le1$, a chart smallness condition, comparison dimensions bounded by $D$, and explicit inequalities among these numbers), and `SharedWidthPreparedCenteredShortForecastGoodModelInterface` for $\mathrm{prep},U,b,S,hR,h\sigma,\mathrm{selection},\mathrm{stride},N,P_{\mathrm{detect}},u_{\mathrm{Source}},p_{\mathrm{Model}},p_{\mathrm{Slice}},V_{\mathrm{tail}},\tau,u,p,\mathrm{forecastCap},hb,o,bW,\mu$ and $P_{\mathrm{chart}},Q_{\mathrm{stride}},P_{\mathrm{master}},P_{\mathrm{late}},p_{\mathrm{Gain}},P_{\mathrm{physical}},\mathrm{coarseTarget},B_0,\mathrm{gainLog},\mathrm{gain},P_{\mathrm{good}},Q_{\mathrm{good}},\mathrm{spatialEmbedding}$ (a proposition defined by OpenAI). Then `SharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface` holds for the same data together with $P_{\mathrm{prod}}$ (a proposition defined by OpenAI).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.sharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface_of_goodModel_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.sharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface_of_goodModel` (in `lean/OAI/Combinatorics/Progressions/Sampling/SharedWidthPreparedShortForecastProductiveModelAttachment.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B290`, `OAIE3v2B291` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/SharedWidthPreparedShortForecastProductiveModelAttachment.lean (declaration OAI.Erdos3.VectorPolynomial.sharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface_of_goodModel)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B290
import Definitions.Def_OAIE3v2B291

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite

theorem sharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface_of_goodModel_s2
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
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
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)] [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [μ.IsAddLeftInvariant]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j)))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (B0 gainLog gain Pgood : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (Pprod : ℝ)
    {D : ℝ}
    (hBounds : PreparedCenteredForecastProductiveBounds (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S) (selection := selection)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      Pchart Qstride Pmaster Plate Pphysical coarseTarget gainLog Pprod D)
    (hModel : SharedWidthPreparedCenteredShortForecastGoodModelInterface (m := m) (nX := nX) (M := M) (X₀ := X₀) (J₀ := J₀) (Q := Q)
      (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (bW := bW) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      B0 gainLog gain Pgood Qgood spatialEmbedding) :
    SharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface (m := m) (nX := nX) (M := M) (X₀ := X₀) (J₀ := J₀) (Q := Q)
      (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (bW := bW) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      B0 gainLog gain Pgood Qgood spatialEmbedding Pprod := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
