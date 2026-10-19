-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedUniformDegreeProductiveSourceRawBounds_s2
-- name    : OAI.Erdos3.VectorPolynomial.preparedUniformDegreeProductiveSourceRawBounds_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:17:42.817106+00:00
-- url     : https://prove2.me/theorems/dcbbf861-7bcb-4d97-a51e-ae779ee844a0
-- title:
--   Explicit parameter inequalities and an early native source geometry give the prepared short forecast source raw bounds
-- statement:
--   All named objects below are defined by OpenAI. Let $m, n_X, M$ be natural numbers, $X_0, J_0$ types, and `prep` a `RankPreparationFamily X₀ J₀ m` (a family of $m$ rank-preparation layers); assume decidable equality on each layer's coordinate type `(prep j).Coord`. For each $j < m$ let $U_j$ be a real subspace of $\mathbb{R}^{(\mathrm{prep}\ j).\mathrm{Coord}}$ and $b_j$ a basis, indexed by $\{0,\dots,\texttt{preparedSamplerTransverse prep j}-1\}$, of the orthogonal complement of the Euclidean copy of $U_j$. Let $R_j, \sigma_j$ be reals. Write $K_0$ = `modularInitialBlockCount m (nX + m * M)`, $G$ = `EnlargedPreparedCommonKernel m K₀`, $\mathcal{B}$ = `EnlargedPreparedCommonSamplerBlock prep K₀`, and let $S$ be a `LayerSamplerScale` with kernel type $G$, continuous index types `PreparedSamplerContinuous prep`, transverse dimensions `preparedSamplerTransverse prep`, coordinate types `(prep j).Coord`, block types $\mathcal{B}$, and data $U, b, R, \sigma$ (scale value `S.value`). Write $|V|$ for the cardinality of `LayerSamplerVariables G (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) 𝓑`.
--
--   Let `selection` be an embedding of the one-element type $\{0\}$ into $G$; $P_{\mathrm{detect}}$ a polynomial with natural-number coefficients; $u_{\mathrm{Source}}, p_{\mathrm{Model}}, p_{\mathrm{Slice}}, u, p$, `forecastCap` reals; $V_{\mathrm{tail}} : \{0,\dots,m-1\} \to \mathbb{R}_{\ge 0}$; reals $P_{\mathrm{chart}}, Q_{\mathrm{stride}}, P_{\mathrm{master}}, P_{\mathrm{late}}, P_{\mathrm{physical}}$, `coarseTarget`, $p_{\mathrm{Radius}}, P_{\mathrm{scale}}, P_{\mathrm{seed}}, Q_w$, `gainLog`, `gain`, $V_{\log}, D$, `target`, $P_k, P_\rho$; and a natural number $Q_{\mathrm{good}}$. Let `geometry` be an `AllocatedEarlyNativeSourceGeometryGeneral` for the data $(\mathcal{B}, U, b, S)$ with $s = 0$, $n_X$, and parameters $P_{\mathrm{chart}}, P_{\mathrm{scale}}, D$, target, $P_k, P_\rho, Q_{\mathrm{stride}}$, `allocatedModelTestLog uSource pModel` and $\max(e^{p_{\mathrm{Radius}}}, 0)$ (a structure of OpenAI recording scale inequalities such as $R_j^{\pm 1} \le e^{P_{\mathrm{scale}}}$ and a lower bound on `S.value`, together with auxiliary data).
--
--   Assume:
--   - $0 < m$, $0 < n_X$, and $|(\mathrm{prep}\ j).\mathrm{Coord}| \le M$ for all $j$;
--   - $0 \le p_{\mathrm{Radius}}$, $0 \le P_{\mathrm{seed}}$, $0 \le Q_w$, $0 \le V_{\log}$, $0 \le$ gainLog;
--   - $1 \le Q_{\mathrm{good}}$ and $Q_{\mathrm{good}} \le e^{V_{\log}}$;
--   - $0 \le P_{\mathrm{master}} \le P_{\mathrm{late}}$; $D \le P_{\mathrm{master}}$; $n_X \le P_{\mathrm{master}}$; $p_{\mathrm{Radius}} \le P_{\mathrm{master}}$; $P_{\mathrm{scale}} \le P_{\mathrm{late}}$; `allocatedWitnessScaleLog Pseed Qw` $\le P_{\mathrm{late}}$; $Q_{\mathrm{stride}} \le P_{\mathrm{master}}$; $P_{\mathrm{physical}} \le P_{\mathrm{master}}$;
--   - $e^{-\mathrm{gainLog}} \le$ gain;
--   - $0 \le P_{\mathrm{chart}}$, $n_X \le P_{\mathrm{chart}}$, gainLog $\le P_{\mathrm{chart}}$;
--   - $\mathrm{S.value} \le \exp(\texttt{allocatedWitnessScaleLog Pseed Qw})$;
--   - for all $j$ and $i$ with $\mathrm{S.value}^{j+1} < $ `basisAxisScale (b j) i`:
--   $$8\cdot\texttt{probabilityProfileLipschitz}\cdot \texttt{physicalBadProductGap}\bigl(K_0 (n_X + mM),\ \mathrm{gainLog}+8,\ V_{\log},\ Q_{\mathrm{good}}\bigr) \le \frac{\texttt{layerSamplerGapWidth}\ \mathcal{B}\ R\ (j,i)}{2}\cdot\frac{\texttt{basisAxisScale}(b_j, i)}{\mathrm{S.value}^{j+1}};$$
--   - $\bigl(\texttt{normalizedTupleNarrowWidth}(\{0,\dots,n_X-1\}, \mathcal{T}, \mathrm{selection}, \kappa, P_{\mathrm{physical}}, \mathrm{coarseTarget})\bigr)^{-1} \le e^{P_{\mathrm{late}}}$, where $\mathcal{T}$ is `PrincipalTupleIndex 𝓑 (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))`, $\kappa$ = `allocatedDetectedKernelCutoff 0 G |V| Pdetect L L (θ/2)`, $L$ = `allocatedModelTestLog uSource pModel`, and $\theta$ = `forecastAugmentedUnitThreshold u p` $\bigl(e^{p_{\mathrm{Slice}}|V|}\bigr)$ $\bigl(\max(1, 4\prod_j \texttt{earlyConstantDensityCap}\ |\texttt{PreparedSamplerContinuous prep j}|\ (\texttt{preparedSamplerTransverse prep j})\ R_j\ V_{\mathrm{tail}}(j))\bigr)$ forecastCap.
--
--   Let $B_0$ = `preparedUniformDegreeProductiveCertificateBudget M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog` $= 1 + M + n_X + p_{\mathrm{Radius}} + P_{\mathrm{scale}} + P_{\mathrm{seed}} + Q_w + (\mathrm{gainLog}+8) + V_{\log}$, and $P_{\mathrm{width}} = 4(P_{\mathrm{late}}+8)^2$. Then `PreparedShortForecastSourceRawBounds prep U b S selection Pdetect uSource pModel pSlice Vtail u p forecastCap Pchart Qstride Pmaster Plate Pphysical coarseTarget B₀ Vlog gainLog gain P_width Qgood D` holds (a structure of OpenAI collecting raw bounds, beginning with a certified same-scale bad-product interface for every budget at least $B_0$, and including $0 < n_X$), and $P_{\mathrm{late}} \le P_{\mathrm{width}}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedUniformDegreeProductiveSourceRawBounds_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.preparedUniformDegreeProductiveSourceRawBounds` (in `lean/OAI/Combinatorics/Progressions/Polynomial/PreparedUniformDegreeProductiveSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B286` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/PreparedUniformDegreeProductiveSource.lean (declaration OAI.Erdos3.VectorPolynomial.preparedUniformDegreeProductiveSourceRawBounds)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B286

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

theorem preparedUniformDegreeProductiveSourceRawBounds_s2
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (u p forecastCap : ℝ)
    {Pchart Qstride Pmaster Plate Pphysical coarseTarget pRadius Pscale Pseed Qw
      gainLog gain Vlog D target Pk Prho : ℝ} (Qgood : ℕ)
    (geometry : AllocatedEarlyNativeSourceGeometryGeneral
      (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
      (U := U) (basis := b) (S := S) (s := 0) (nX := nX)
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog uSource pModel)
      (Real.toNNReal (Real.exp pRadius)))
    (hm : 0 < m) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hpRadius : 0 ≤ pRadius) (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw)
    (hVlog : 0 ≤ Vlog) (hg : 0 ≤ gainLog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hD : D ≤ Pmaster) (hnMaster : (nX : ℝ) ≤ Pmaster)
    (hRadiusMaster : pRadius ≤ Pmaster) (hScaleLate : Pscale ≤ Plate)
    (hWitnessLate : allocatedWitnessScaleLog Pseed Qw ≤ Plate)
    (hStrideMaster : Qstride ≤ Pmaster) (hPhysicalMaster : Pphysical ≤ Pmaster)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hchart : 0 ≤ Pchart) (hnChart : (nX : ℝ) ≤ Pchart)
    (hgChart : gainLog ≤ Pchart)
    (hS : (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M))
          (gainLog + 8) Vlog Qgood ≤
          (layerSamplerGapWidth
            (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
            R ⟨j, i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)))
    (hξLate : (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) selection
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog uSource pModel) (allocatedModelTestLog uSource pModel) ((forecastAugmentedUnitThreshold u p (Real.exp (pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))) (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j))) forecastCap) / 2)) Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate) :
    let baseB0 := preparedUniformDegreeProductiveCertificateBudget
      M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
    let Pwidth := 4 * (Plate + 8) ^ 2
    PreparedShortForecastSourceRawBounds prep U b S selection Pdetect uSource pModel pSlice
      Vtail u p forecastCap Pchart Qstride Pmaster Plate Pphysical coarseTarget
      baseB0 Vlog gainLog gain Pwidth Qgood D ∧ Plate ≤ Pwidth := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
