-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedUniformDegreeGeometryModel
-- name    : OAI.Erdos3.VectorPolynomial.preparedUniformDegreeGeometryModel
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T02:27:59.364981+00:00
-- url     : https://prove2.me/theorems/a5e10e64-f6c0-47b2-a549-6f3763f26f84
-- title:
--   Degree-zero detector bounds give the centered forecast model interface and a width bound
-- statement:
--   Work in OpenAI's layer-sampler setting with detector size $s=0$: natural numbers $m,n_X$ (implicit); a finite type $G$ with decidable equality; finite types $I_j$ and natural numbers $n_j$ ($j<m$); a finite type $B_a$ for each $a$ in `LayerSamplerAxis I n`; finite types $J_j$, subspaces $U_j\subseteq\mathbb{R}^{J_j}$ and bases $\mathrm{basis}_j$, indexed by $\mathrm{Fin}\,n_j$, of the orthogonal complement of `euclideanSubspace (U j)`; reals $R_j>0$, $\sigma_j>0$ ($hR$, $h\sigma$); a `LayerSamplerScale B U basis R σ` $S$; an embedding $\mathrm{selection}:\mathrm{Fin}(0+1)\hookrightarrow G$; $\mathrm{stride},N:\mathrm{Fin}\,n_X\to\mathbb{N}$; reals $u,p,p_{\mathrm{Model}},p_{\mathrm{Slice}},\tau,\mathrm{forecastCap}$; a polynomial $P_{\mathrm{detect}}\in\mathbb{N}[X]$; $V_{\mathrm{tail}}:\mathrm{Fin}\,m\to\mathbb{R}_{\ge0}$; $hb$ (the $\mathbb{Z}$-span of the range of $\mathrm{basis}_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`); orthonormal bases $o_j$ of `euclideanSubspace (U j)`; each `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` a $\mathbb{Z}$-lattice; left-invariant probability measures $\nu_j$ on the quotient tori; compact Borel structures on `CoefficientTorus U` over `LayerSamplerVariables G I n B` and over $\mathrm{Fin}(0+1)$, with left-invariant probability measures $\mu$ and $\mu_{\mathrm{rows}}$; finite types $Q_j$ with $\mathbb{Z}$-bases $bW_j$ of the lattice above; and a Borel measurable structure on `SiteTorus (Finset (Fin (0 + 1))) U`. Write $u_{\mathrm{Source}}=u+2p+1$, $p_{\mathrm{Detect}}$ for `allocatedModelTestLog uSource pModel` ($=2u_{\mathrm{Source}}+5p_{\mathrm{Model}}+12$), $C$ for `sampledSupportedSlicedDetectionConstant 0 Pdetect`, $C_{\mathrm{tail}}=4\prod_j$`earlyConstantDensityCap |I_j| n_j R_j (Vtail j)`, $K_{\mathrm{slice}}=e^{p_{\mathrm{Slice}}\,|\mathrm{LayerSamplerVariables}\ G\ I\ n\ B|}$, and $\alpha$ for `forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap`.
--
--   Let $P_{\mathrm{chart}},P_{\mathrm{scale}},D,\mathrm{target},P_k,P_\rho,Q_{\mathrm{stride}},P_{\mathrm{master}},P_{\mathrm{late}},p_{\mathrm{Gain}},P_{\mathrm{physical}},\mathrm{coarseTarget},p_{\mathrm{Radius}}$ be reals. Assume: `PreparedUniformDegreeDirectScalarBounds m 0 nX |LayerSamplerVariables G I n B| C Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius uSource pModel pSlice` (a conjunction of explicit inequalities); `PreparedUniformDegreeGeometryAt B U basis S 0 C nX Pchart Pscale D target Pk Prho Qstride pDetect pRadius (2 uSource + 4 pModel + 7) pGain`; $R_j\le1$, $R_j^{-1}\le e^{p_{\mathrm{Radius}}}$, $\sigma_j\le1$; $S.\mathrm{value}\le e^{P_{\mathrm{late}}}$; for all $j$ and $i\in I_j$, with $r_j$ the number of subsets of $\mathrm{Fin}\,1$ of size at most $j+1$, both `positiveModerateSpectrumBlockCount j r_j ((layerTailDegree m + 1) r_j)` and `uniformSpectrumBlockCount j r_j ((j+1) r_j)` are at most $|B_{\langle j,\mathrm{inr}\,i\rangle}|$; $(0+1)(0+3)\le|G|$; $u\ge0$, $p\ge0$; $p_{\mathrm{Slice}}\,|\mathrm{LayerSamplerVariables}\ G\ I\ n\ B|\le p$; $C_{\mathrm{tail}}\le e^{p}$; and $0\le\mathrm{forecastCap}\le e^{p}$. Then both hold: `SharedWidthPreparedCenteredForecastModelInterface Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget` for the data $B,U,\mathrm{basis},S,hR,h\sigma,\mathrm{selection},\mathrm{stride},N,P_{\mathrm{detect}},u_{\mathrm{Source}},p_{\mathrm{Model}},p_{\mathrm{Slice}},V_{\mathrm{tail}},\tau,u,p,\mathrm{forecastCap},hb,o,\mu$ (a proposition defined by OpenAI); and the reciprocal of `normalizedTupleNarrowWidth (Fin nX) (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedKernelCutoff 0 G |LayerSamplerVariables G I n B| Pdetect pDetect pDetect (α/2)) Pphysical coarseTarget` is at most $e^{P_{\mathrm{late}}}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedUniformDegreeGeometryModel` in `lean/OAI/Combinatorics/Progressions/Polynomial/PreparedUniformDegreeProductiveSourceModel.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1347`, `OAIErdos3B1353` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/PreparedUniformDegreeProductiveSourceModel.lean#L152

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1347
import Definitions.Def_OAIErdos3B1353

namespace OAI

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (Fin.val j + 1))
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (τ u p forecastCap : ℝ)

variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (Fin.val j + 1))
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (u p : ℝ)
local notation "uSource" => u + 2 * p + 1
variable (Pdetect : Polynomial ℕ) (pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog uSource pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (τ forecastCap : ℝ)
local notation "α" => forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap

variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
variable [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

include ν bW μrows in
theorem preparedUniformDegreeGeometryModel
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m 0 nX
      (Fintype.card (LayerSamplerVariables G I n B))
      (sampledSupportedSlicedDetectionConstant 0 Pdetect)
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius uSource pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S 0
      (sampledSupportedSlicedDetectionConstant 0 Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride pDetect pRadius
      (2 * uSource + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσone : ∀ j, σ j ≤ 1)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hcapacity : (0 + 1) * (0 + 3) ≤ Fintype.card G)
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hCtail : Ctail ≤ Real.exp p)
    (hForecastCap : 0 ≤ forecastCap) (hForecastCapP : forecastCap ≤ Real.exp p) :
    SharedWidthPreparedCenteredForecastModelInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) («uSource» := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget ∧
    (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff 0 G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect pDetect pDetect (α / 2)) Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate := by
  sorry

end Erdos3.VectorPolynomial
end OAI
