-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedFiniteScheduleDegreeGeometryModel_s2
-- name    : OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleDegreeGeometryModel_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:28:41.785221+00:00
-- url     : https://prove2.me/theorems/b2392307-40d3-4c1c-9b20-35b651fd0694
-- title:
--   Uniform-degree scalar bounds and geometry give scheduled degree-model availability
-- statement:
--   Work in OpenAI's layer-sampler setting: natural numbers $m,s,n_X$ (implicit); a finite type $G$ with decidable equality; finite types $I_j$ and natural numbers $n_j$ ($j<m$); a finite type $B_a$ for each $a$ in `LayerSamplerAxis I n` (the sigma type $\Sigma_j\,(I_j\oplus\mathrm{Fin}\,n_j)$); finite types $J_j$, subspaces $U_j\subseteq\mathbb{R}^{J_j}$ and bases $\mathrm{basis}_j$, indexed by $\mathrm{Fin}\,n_j$, of the orthogonal complement of `euclideanSubspace (U j)`; reals $R_j>0$, $\sigma_j>0$ ($hR$, $h\sigma$); a `LayerSamplerScale B U basis R σ` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); an embedding $\mathrm{selection}:\mathrm{Fin}(s+1)\hookrightarrow G$; $\mathrm{stride},N:\mathrm{Fin}\,n_X\to\mathbb{N}$; reals $\mathrm{sourceU},p_{\mathrm{Model}},p_{\mathrm{Slice}},\tau$; a polynomial $P_{\mathrm{detect}}\in\mathbb{N}[X]$; $V_{\mathrm{tail}}:\mathrm{Fin}\,m\to\mathbb{R}_{\ge0}$; $hb$ (the $\mathbb{Z}$-span of the range of $\mathrm{basis}_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`); orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; each `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` a $\mathbb{Z}$-lattice; left-invariant probability measures $\nu_j$ on the quotient of `euclideanSubspace (U j)` by that lattice; a compact Borel structure on `CoefficientTorus U` over `LayerSamplerVariables G I n B` with a left-invariant probability measure $\mu$; finite types $Q_j$ and $\mathbb{Z}$-bases $bW_j$, indexed by $Q_j$, of the lattice above. Write $p_{\mathrm{Detect}}$ for `allocatedModelTestLog sourceU pModel` ($=2\,\mathrm{sourceU}+5p_{\mathrm{Model}}+12$).
--
--   Let $C_{\mathrm{detect}}$ be the natural number `sampledSupportedSlicedDetectionConstant s Pdetect` (hypothesis $hC_{\mathrm{detect}}$; a constant chosen by OpenAI from an existence statement), assume $s\le m$, and let $P_{\mathrm{chart}},P_{\mathrm{scale}},D,\mathrm{target},P_k,P_\rho,Q_{\mathrm{stride}},P_{\mathrm{master}},P_{\mathrm{late}},p_{\mathrm{Gain}},P_{\mathrm{physical}},\mathrm{coarseTarget},p_{\mathrm{Radius}}$ be reals. Assume: `PreparedUniformDegreeDirectScalarBounds m s nX |LayerSamplerVariables G I n B| Cdetect Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius sourceU pModel pSlice` (a conjunction of explicit inequalities among these numbers); `PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX Pchart Pscale D target Pk Prho Qstride pDetect pRadius (2 sourceU + 4 pModel + 7) pGain` (the existence of an `AllocatedEarlyNativeSourceGeometryGeneral` together with explicit gain and `scalarKernelCutoff` inequalities); $R_j\le1$, $R_j^{-1}\le e^{p_{\mathrm{Radius}}}$, $\sigma_j\le1$ for all $j$; $S.\mathrm{value}\le e^{P_{\mathrm{late}}}$; for all $j$ and $i\in\mathrm{Fin}\,n_j$, with $r_j$ the number of subsets of $\mathrm{Fin}(s+1)$ of size at most $j+1$, both `positiveModerateSpectrumBlockCount j r_j ((layerTailDegree m + 1) r_j)` and `uniformSpectrumBlockCount j r_j ((j+1) r_j)` are at most $|B_{\langle j,\mathrm{inr}\,i\rangle}|$; and $(s+1)(s+3)\le|G|$. Then `PreparedScheduledDegreeModelAvailability Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget` holds for the data $B,U,\mathrm{basis},S,hR,h\sigma,\mathrm{selection},\mathrm{stride},N,P_{\mathrm{detect}},\mathrm{sourceU},p_{\mathrm{Model}},p_{\mathrm{Slice}},V_{\mathrm{tail}},\tau,hb,o,\mu$. This is the proposition (defined by OpenAI) that for all reals $u,p,\mathrm{forecastCap}$ with $\mathrm{sourceU}=u+2p+1$, $u,p\ge0$, $p_{\mathrm{Slice}}\,|\mathrm{LayerSamplerVariables}\ G\ I\ n\ B|\le p$, $C_{\mathrm{tail}}\le e^{p}$ (where $C_{\mathrm{tail}}=4\prod_j$`earlyConstantDensityCap |I_j| n_j R_j (Vtail j)`) and $0\le\mathrm{forecastCap}\le e^{p}$, the proposition `SharedWidthPreparedCenteredForecastModelDegreeInterface … Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget` holds and the reciprocal of an explicit `normalizedTupleNarrowWidth` is at most $e^{P_{\mathrm{late}}}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleDegreeGeometryModel_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleDegreeGeometryModel` (in `lean/OAI/Combinatorics/Progressions/Polynomial/PreparedFiniteForwardDegreeModelAttachment.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B285` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/PreparedFiniteForwardDegreeModelAttachment.lean (declaration OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleDegreeGeometryModel)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B285

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section Availability

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (sourceU : ℝ)
variable (Pdetect : Polynomial ℕ) (pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog sourceU pModel
variable (τ : ℝ)

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

include ν bW in

theorem preparedFiniteScheduleDegreeGeometryModel_s2
    (Cdetect : ℕ)
    (hCdetect : Cdetect = sampledSupportedSlicedDetectionConstant s Pdetect)
    (hsm : s ≤ m)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B)) Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX
      Pchart Pscale D target Pk Prho Qstride pDetect pRadius
      (2 * sourceU + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσone : ∀ j, σ j ≤ 1)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hcapacity : (s + 1) * (s + 3) ≤ Fintype.card G) :
    PreparedScheduledDegreeModelAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  sorry

end Availability

end Erdos3.VectorPolynomial

end

end OAI
end
