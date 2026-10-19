-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedUniformDegreeDirectSource_of_geometry_s2
-- name    : OAI.Erdos3.VectorPolynomial.preparedUniformDegreeDirectSource_of_geometry_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:24:33.768771+00:00
-- url     : https://prove2.me/theorems/1dd0dbc4-6e28-4b1a-a2d0-09f1cca3193e
-- title:
--   Uniform-degree scalar bounds and geometry give the free-trim shared-width interface
-- statement:
--   Work in OpenAI's layer-sampler setting: natural numbers $m,s,n_X$ with $s\le m$; a finite type $G$ with decidable equality; finite types $I_j$ and natural numbers $n_j$ ($j<m$); a finite type $B_a$ for each $a$ in `LayerSamplerAxis I n` (the sigma type $\Sigma_j\,(I_j\oplus\mathrm{Fin}\,n_j)$); finite types $J_j$, subspaces $U_j\subseteq\mathbb{R}^{J_j}$, and bases $\mathrm{basis}_j$, indexed by $\mathrm{Fin}\,n_j$, of the orthogonal complement of `euclideanSubspace (U j)` ($U_j$ viewed inside Euclidean space); reals $R_j>0$, $\sigma_j>0$ (hypotheses `hR`, `hσ`); and $S$ a `LayerSamplerScale B U basis R σ` (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Also fixed are finite types $Q_j$; the hypothesis `hb` that the $\mathbb{Z}$-span of the range of $\mathrm{basis}_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`; orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; $\mathbb{Z}$-bases $bW_j$, indexed by $Q_j$, of the lattice `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`, assumed to be a $\mathbb{Z}$-lattice; left-invariant probability measures $\nu_j$ on the quotient of `euclideanSubspace (U j)` by that lattice; compact Borel structures on `CoefficientTorus U` over `LayerSamplerVariables G I n B` and over $\mathrm{Fin}(s+1)$ with left-invariant probability measures $\mu$ and $\mu_{\mathrm{rows}}$ on them; and a Borel measurable structure on `SiteTorus (Finset (Fin (s + 1))) U`. Further fixed: an embedding $\mathrm{selection}:\mathrm{Fin}(s+1)\hookrightarrow G$, $\mathrm{stride},N:\mathrm{Fin}\,n_X\to\mathbb{N}$, a polynomial $P_{\mathrm{detect}}\in\mathbb{N}[X]$, reals $u,p_{\mathrm{Model}},p_{\mathrm{Slice}},\alpha,\tau$, and $V_{\mathrm{tail}}:\mathrm{Fin}\,m\to\mathbb{R}_{\ge0}$. Write $p_{\mathrm{Detect}}$ for `allocatedModelTestLog u pModel` ($=2u+5p_{\mathrm{Model}}+12$) and $C$ for the natural number `sampledSupportedSlicedDetectionConstant s Pdetect` (chosen by OpenAI from an existence statement).
--
--   Let $P_{\mathrm{chart}},P_{\mathrm{scale}},D,\mathrm{target},P_k,P_\rho,Q_{\mathrm{stride}},P_{\mathrm{master}},P_{\mathrm{late}},p_{\mathrm{Gain}},P_{\mathrm{physical}},\mathrm{coarseTarget},p_{\mathrm{Radius}}$ be real numbers. Assume: `PreparedUniformDegreeDirectScalarBounds m s nX |LayerSamplerVariables G I n B| C Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius u pModel pSlice` (a conjunction of explicit inequalities among these numbers); `PreparedUniformDegreeGeometryAt B U basis S s C nX Pchart Pscale D target Pk Prho Qstride pDetect pRadius (2u+4pModel+7) pGain` (the existence of an `AllocatedEarlyNativeSourceGeometryGeneral` structure together with explicit lower bounds on a gain and upper bounds on a `scalarKernelCutoff` for every $\alpha'\ge e^{-(2u+4p_{\mathrm{Model}}+7)}$); $R_j\le 1$, $R_j^{-1}\le e^{p_{\mathrm{Radius}}}$ and $\sigma_j\le 1$ for all $j$; $S.\mathrm{value}\le e^{P_{\mathrm{late}}}$; for all $j$ and $i\in\mathrm{Fin}\,n_j$, writing $r_j$ for the number of subsets of $\mathrm{Fin}(s+1)$ of size at most $j+1$ (`boundedBooleanJetRows`), both `positiveModerateSpectrumBlockCount j r_j ((layerTailDegree m + 1) r_j)` and `uniformSpectrumBlockCount j r_j ((j+1) r_j)` are at most $|B_{\langle j,\mathrm{inr}\,i\rangle}|$; $(s+1)(s+3)\le|G|$; and $e^{-(2u+4p_{\mathrm{Model}}+7)}\le\alpha\le 1$. Then `PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget` holds for the data $B,U,\mathrm{basis},S,hR,h\sigma,\mathrm{selection},\mathrm{stride},N,P_{\mathrm{detect}},u,p_{\mathrm{Model}},p_{\mathrm{Slice}},V_{\mathrm{tail}},\alpha,\tau,hb,o$ (a proposition defined by OpenAI, universally quantified over stride and chart bounds, a spatial tolerance, a width, residue cells, families of vector polynomials of layer-sampling rank and nilmanifold detection data).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedUniformDegreeDirectSource_of_geometry_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.preparedUniformDegreeDirectSource_of_geometry` (in `lean/OAI/Combinatorics/Progressions/Polynomial/PreparedUniformDegreeDirectMasterBudget.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B285` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/PreparedUniformDegreeDirectMasterBudget.lean (declaration OAI.Erdos3.VectorPolynomial.preparedUniformDegreeDirectSource_of_geometry)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B285

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section Consumer

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
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog u pModel
variable (α τ : ℝ)
variable {P : ℝ}

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

include hb o bW μ ν μrows hR hσ in

theorem preparedUniformDegreeDirectSource_of_geometry_s2 (hsm : s ≤ m)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B))
      (sampledSupportedSlicedDetectionConstant s Pdetect)
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius u pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s
      (sampledSupportedSlicedDetectionConstant s Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride pDetect pRadius
      (2 * u + 4 * pModel + 7) pGain)
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
    (hcapacity : (s + 1) * (s + 3) ≤ Fintype.card G)
    (hαlower : Real.exp (-(2 * u + 4 * pModel + 7)) ≤ α) (hαone : α ≤ 1) :
    PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  sorry

end Consumer
end Erdos3.VectorPolynomial

end

end OAI
end
