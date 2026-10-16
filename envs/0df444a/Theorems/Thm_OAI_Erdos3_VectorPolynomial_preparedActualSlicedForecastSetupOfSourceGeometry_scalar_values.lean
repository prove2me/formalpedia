-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedActualSlicedForecastSetupOfSourceGeometry_scalar_values
-- name    : OAI.Erdos3.VectorPolynomial.preparedActualSlicedForecastSetupOfSourceGeometry_scalar_values
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:53:01.0755+00:00
-- url     : https://prove2.me/theorems/643d5290-5431-4203-9379-62f61c32ad38
-- title:
--   The scalar parameters of the prepared source sliced forecast setup
-- statement:
--   Fix types $X_0,J_0$, a natural number $m$ and a `RankPreparationFamily X₀ J₀ m` $L$ (a family of $m$ rank-preparation layers, the $j$-th with a finite coordinate type $\mathrm{Coord}_j$), a natural number $J_{\mathrm{alloc}}$, subspaces $U_j\subseteq\mathbb{R}^{\mathrm{Coord}_j}$, bases $b_j$ of the orthogonal complement of `euclideanSubspace (U j)` indexed by $\mathrm{Fin}$(`preparedSamplerTransverse L j`), orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by `PreparedSamplerContinuous L j`, reals $R_j,\sigma_j$, a `LayerSamplerScale` $S$ for the kernel `EnlargedPreparedCommonKernel m Jalloc` and blocks `EnlargedPreparedCommonSamplerBlock L Jalloc`, finite types $E^{\mathrm{out}}_j$, $\mathbb{Z}$-bases $bW_j$, indexed by $E^{\mathrm{out}}_j$, of the lattice `latticeSection (standardEuclideanLattice Coord_j) (euclideanSubspace (U j))` (assumed a $\mathbb{Z}$-lattice), and the hypothesis $hb$ that the $\mathbb{Z}$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`. Let $M,n_X$ be natural numbers with $m>0$ and $|\mathrm{Coord}_j|\le M$ for all $j$; let $p_{\mathrm{Radius}},\mathrm{gainLog},Q_{\mathrm{stride}},P_F,P_{\mathrm{chart}},\mathrm{cost}\ge0$ and $P_{\dim}$ be reals; assume `mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)` $\le e^{P_{\mathrm{chart}}}$, $0<R_j\le1$, $R_j^{-1}\le e^{p_{\mathrm{Radius}}}$ and $\sigma_j\le1$ for all $j$; let $\mathrm{forward}_j\ge0$ with $\|\Phi_j w\|\le\mathrm{forward}_j\|w\|$ and $\mathrm{forward}_j\le e^{P_F}$, where $\Phi_j$ is `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)` (a continuous linear equivalence from $\mathbb{R}^{\mathrm{Coord}_j}$ to `euclideanSubspace (U j)` $\times\mathbb{R}^{\mathrm{Fin}(\cdot)}$); let $\mathrm{inverse}_j\ge0$ with $\|\Phi_j^{-1}w\|\le\mathrm{inverse}_j\|w\|$; let $C_{\mathrm{detect}}$ be a natural number and $B_{\mathrm{struct}},P_{\mathrm{scale}},D_{\mathrm{geometry}},\mathrm{target},P_k,P_\rho,p_{\mathrm{Detect}},a_{\mathrm{Detect}},\mathrm{detectionGain}$ reals with $\mathrm{inverse}_j\le e^{B_{\mathrm{struct}}}$ and `PreparedUniformDegreeGeometryAt (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S 0 Cdetect nX Bstruct Pscale Dgeometry target Pk Prho Qstride pDetect pRadius aDetect detectionGain` (a proposition defined by OpenAI: an `AllocatedEarlyNativeSourceGeometryGeneral` exists, plus explicit gain and cutoff inequalities). Let $s$ be `preparedActualSlicedForecastSetupOfSourceGeometry …` built from all of these data (an `ActualFixedSpatialForecastSetup` over $X=\mathrm{Fin}\,n_X$, a structure bundling numerical parameters with inequalities), and write $D_0$ for `allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc)` (cast to $\mathbb{R}$). Then $s.P$ = `preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost`; $s.P_{\mathrm{scale}}=D_0+p_{\mathrm{Radius}}+1$; $s.P_{\mathrm{bad}}$ = `preparedSlicedForecastBadLog m nX Qstride gainLog`; $s.P_{\mathrm{pres}}=\mathrm{cost}+1$; $s.P_\kappa$ = `preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart`; $s.\kappa$ = `forecastGeometricJacobian U b R S.value (preparedForecastGridVolume L Jalloc U b S) (exp (-(gainLog + nX + 8)))` (over $X=\mathrm{Fin}\,n_X$ and continuous index types `PreparedSamplerContinuous L`; the reciprocal of an explicit product of scales); $s.P_{\mathrm{cap}}$ = `preparedSlicedForecastPrimitiveCap`; $s.P_\tau=\mathrm{gainLog}+n_X+8$; $s.P_K=p_{\mathrm{Radius}}$; $s.P_F=P_F$; and $s.D=D_0$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedActualSlicedForecastSetupOfSourceGeometry_scalar_values` in `lean/OAI/Combinatorics/Progressions/Sampling/PreparedSourceSlicedForecastNumerics.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1348` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/PreparedSourceSlicedForecastNumerics.lean#L239

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1348

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]

theorem preparedActualSlicedForecastSetupOfSourceGeometry_scalar_values {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)),
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    {Cdetect : ℕ} {Bstruct Pscale Dgeometry target Pk Prho pDetect aDetect detectionGain : ℝ}
    (hInverseBound : ∀ j, inverse j ≤ Real.exp Bstruct)
    (hgeometry : PreparedUniformDegreeGeometryAt
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S 0 Cdetect nX
      Bstruct Pscale Dgeometry target Pk Prho Qstride pDetect pRadius aDetect detectionGain)
 :
    let s := preparedActualSlicedForecastSetupOfSourceGeometry (nX := nX)
      L Jalloc U b o S bW hb hm hCoord Pdim hpRadius hGain hQstride hPF hChart
      hcost hratio hR hRone hRinv hσone forward hforward hforwardBound
      inverse hinverse hchart hInverseBound hgeometry
    s.P = preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ∧
    s.Pscale = allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ∧
    s.Pbad = preparedSlicedForecastBadLog m nX Qstride gainLog ∧
    s.Ppres = cost + 1 ∧
    s.Pκ = preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ∧
    s.κ = forecastGeometricJacobian (X := Fin nX) (I := PreparedSamplerContinuous L) U b R S.value
      (preparedForecastGridVolume L Jalloc U b S) (Real.exp (-(gainLog + (nX : ℝ) + 8))) ∧
    s.Pcap = preparedSlicedForecastPrimitiveCap ∧
    s.Pτ = gainLog + nX + 8 ∧ s.PK = pRadius ∧ s.PF = PF ∧
    s.D = allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
