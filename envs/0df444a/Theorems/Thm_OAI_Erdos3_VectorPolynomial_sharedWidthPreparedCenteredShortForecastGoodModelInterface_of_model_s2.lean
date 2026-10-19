-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_sharedWidthPreparedCenteredShortForecastGoodModelInterface_of_model_s2
-- name    : OAI.Erdos3.VectorPolynomial.sharedWidthPreparedCenteredShortForecastGoodModelInterface_of_model_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:56:40.497933+00:00
-- url     : https://prove2.me/theorems/c8a81397-64d8-40f3-aa96-5e2636685b7f
-- title:
--   Good short-forecast bounds and the forecast model interface give the good-model interface
-- statement:
--   All data are binders of the theorem itself, some implicit as marked below (the section variables of the same names are not used). Let $m,n_X,M$ be natural numbers, $X_0,J_0$ types (implicit), and $\mathrm{prep}$ a `RankPreparationFamily X₀ J₀ m` (a family of $m$ rank-preparation layers, the $j$-th with a finite coordinate type $\mathrm{Coord}_j$). Write $G$ for the kernel type `EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))` and $B$ for the blocks `EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))`, and $V$ for `LayerSamplerVariables G (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B`. Let $U_j\subseteq\mathbb{R}^{\mathrm{Coord}_j}$ be subspaces; $b_j$ bases of the orthogonal complement of `euclideanSubspace (U j)` indexed by $\mathrm{Fin}$(`preparedSamplerTransverse prep j`); $R_j,\sigma_j$ reals (implicit) with $R_j>0$, $\sigma_j>0$ ($hR$, $h\sigma$); $S$ a `LayerSamplerScale` over $G$ and $B$ for $U,b,R,\sigma$; $\mathrm{selection}:\mathrm{Fin}(0+1)\hookrightarrow G$; $\mathrm{stride},N:\mathrm{Fin}\,n_X\to\mathbb{N}$; $P_{\mathrm{detect}}\in\mathbb{N}[X]$; reals $u_{\mathrm{Source}},p_{\mathrm{Model}},p_{\mathrm{Slice}}$; $V_{\mathrm{tail}}:\mathrm{Fin}\,m\to\mathbb{R}_{\ge0}$; reals $\tau,u,p,\mathrm{forecastCap}$; finite types $Q_j$ (implicit); $hb$: the $\mathbb{Z}$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`; orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by `PreparedSamplerContinuous prep j`; $\mathbb{Z}$-bases $bW_j$, indexed by $Q_j$, of `latticeSection (standardEuclideanLattice Coord_j) (euclideanSubspace (U j))`, each assumed a $\mathbb{Z}$-lattice; a compact Borel structure on `CoefficientTorus U` over $V$ with a left-invariant probability measure $\mu$; left-invariant probability measures $\nu_j$ on the quotients of `euclideanSubspace (U j)` by the lattices; reals $P_{\mathrm{chart}},Q_{\mathrm{stride}},P_{\mathrm{master}},P_{\mathrm{late}},p_{\mathrm{Gain}},P_{\mathrm{physical}},\mathrm{coarseTarget}$ and $B_0,V_{\log},\mathrm{gainLog},\mathrm{gain},P_{\mathrm{width}},P_0,P_{\mathrm{good}}$; a natural number $Q_{\mathrm{good}}$; an embedding $\mathrm{spatialEmbedding}:\mathrm{Fin}\,2\times\mathrm{Fin}\,n_X\hookrightarrow G$; and a real $D$ (implicit). Assume `SharedWidthPreparedCenteredShortForecastGoodBounds prep U b S selection Pdetect uSource pModel pSlice Vtail u p forecastCap Pchart Qstride Pmaster Plate Pphysical coarseTarget B0 Vlog gainLog gain Pwidth P₀ Pgood Qgood D` (a structure of hypotheses defined by OpenAI: a certified bad-product interface, $n_X>0$, $\sigma_j\le1$, chart smallness, comparison dimensions bounded by $D$, and explicit inequalities among these numbers), and `SharedWidthPreparedCenteredForecastModelInterface Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget` for the data $B,U,b,S,hR,h\sigma,\mathrm{selection},\mathrm{stride},N,P_{\mathrm{detect}},u_{\mathrm{Source}},p_{\mathrm{Model}},p_{\mathrm{Slice}},V_{\mathrm{tail}},\tau,u,p,\mathrm{forecastCap},hb,o,\mu$ (a proposition defined by OpenAI, universally quantified over stride and chart bounds, a tolerance, a width, residue cells and polynomial families). Then `SharedWidthPreparedCenteredShortForecastGoodModelInterface` holds for $\mathrm{prep},U,b,S,hR,h\sigma,\mathrm{selection},\mathrm{stride},N,P_{\mathrm{detect}},u_{\mathrm{Source}},p_{\mathrm{Model}},p_{\mathrm{Slice}},V_{\mathrm{tail}},\tau,u,p,\mathrm{forecastCap},hb,o,bW,\mu$ and $P_{\mathrm{chart}},Q_{\mathrm{stride}},P_{\mathrm{master}},P_{\mathrm{late}},p_{\mathrm{Gain}},P_{\mathrm{physical}},\mathrm{coarseTarget},B_0,\mathrm{gainLog},\mathrm{gain},P_{\mathrm{good}},Q_{\mathrm{good}},\mathrm{spatialEmbedding}$ (a proposition defined by OpenAI).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.sharedWidthPreparedCenteredShortForecastGoodModelInterface_of_model_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.sharedWidthPreparedCenteredShortForecastGoodModelInterface_of_model` (in `lean/OAI/Combinatorics/Progressions/Sampling/SharedWidthPreparedShortForecastSourceModelAttachment.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B291` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/SharedWidthPreparedShortForecastSourceModelAttachment.lean (declaration OAI.Erdos3.VectorPolynomial.sharedWidthPreparedCenteredShortForecastGoodModelInterface_of_model)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B291

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}
variable (prep : RankPreparationFamily X₀ J₀ m)
local notation "kernel" => EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))
local notation "blocks" => EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))
local notation "axes" => PreparedSamplerContinuous prep
local notation "transverse" => preparedSamplerTransverse prep
local notation "coords" => (fun j : Fin m => RankPreparationLayer.Coord (prep j))
variable (U : ∀ j, Submodule ℝ (coords j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (transverse j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := kernel) (I := axes) (n := transverse) (J := coords) blocks U b R σ)
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (0 + 1) ↪ kernel) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (τ u p forecastCap : ℝ)
variable {P : ℝ}

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (axes j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

theorem sharedWidthPreparedCenteredShortForecastGoodModelInterface_of_model_s2
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
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    [μ.IsAddLeftInvariant]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j)))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (B0 Vlog gainLog gain Pwidth P₀ Pgood : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    {D : ℝ}
    (H : SharedWidthPreparedCenteredShortForecastGoodBounds (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S)
      (selection := selection) (Pdetect := Pdetect) (uSource := uSource)
      (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
      (u := u) (p := p) (forecastCap := forecastCap)
      Pchart Qstride Pmaster Plate Pphysical coarseTarget
      B0 Vlog gainLog gain Pwidth P₀ Pgood Qgood D)
    (hModel : SharedWidthPreparedCenteredForecastModelInterface
      (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget) :
    SharedWidthPreparedCenteredShortForecastGoodModelInterface (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (bW := bW) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      B0 gainLog gain Pgood Qgood spatialEmbedding := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
