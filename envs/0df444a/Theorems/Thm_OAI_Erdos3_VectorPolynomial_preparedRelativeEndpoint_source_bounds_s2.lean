-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedRelativeEndpoint_source_bounds_s2
-- name    : OAI.Erdos3.VectorPolynomial.preparedRelativeEndpoint_source_bounds_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:22:24.028555+00:00
-- url     : https://prove2.me/theorems/f5449124-b1c6-4ce7-80f4-487d759dbbf9
-- title:
--   Numerical source bounds for the prepared relative endpoint
-- statement:
--   Let $X, J$ be types, $m$ a natural number and `prep` a `RankPreparationFamily X J m` (a family of $m$ rank-preparation layers, layer $j$ carrying a finite coordinate type $\mathrm{Coord}_j$). Let $M, n_X, J_{\mathrm{alloc}}$ be natural numbers with $|\mathrm{Coord}_j| \le M$ for all $j$; $\sigma : \mathrm{Fin}\,m \to \mathbb R$; $\xi$ real; $S$ a natural number; $N : \mathrm{Fin}\,n_X \to \mathbb N$; and $T, K, \mathrm{seed}, \mathrm{childLog}, P_{\mathrm{dim}}, \mathrm{cost}, p_{\mathrm{radius}}, \mathrm{gainLog}, Q_{\mathrm{stride}}, P_{\mathrm{test}}, E_{\mathrm{compare}}$ reals. Write $D^\ast =$ `allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc)` and $c^\ast =$ `preparedSlicedForecastPrimitiveCap` (reals defined by OpenAI), and $\Sigma_{\mathrm{prep}} = |\Sigma_j\,$`PreparedSamplerContinuous prep j`$|$. Assume, in order:
--   $K \ge 0$; $T \ge 1$; $m \le T$; $n_X + mM \le T$; $D^\ast \le T$; `preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost` $\le T$; $c^\ast \le T$; `preparedSlicedForecastBadLog m nX Qstride gainLog` $\le T$; $\mathrm{cost} \ge 0$; $\mathrm{cost} + 1 \le T$; $P_{\mathrm{test}} \in [0, T]$; $E_{\mathrm{compare}} \in [0, T]$; $p_{\mathrm{radius}} \le T$; $\mathrm{gainLog} + n_X + 8 \le T$; `preparedRelativeEndpointSigmaLog D* c* Ptest Ecompare cost m` $\le K$; `preparedRelativeEndpointCoarseLog D* c* Ptest Ecompare` $\le K$; $(T + 10)^{2m + 20} \le K$; $0 \le \sigma_j \le e^{-K}$ for all $j$; $\xi \le e^{-K}$; `preparedRelativeEndpointMinimumScale seed 0 childLog cost ((T+10)^(2m+20))` $\le S$; and $e^K \le N_i$ for all $i$. (All the named functions are real-valued expressions defined by OpenAI.)
--
--   Then, with $L_s =$ `preparedSlicedForecastSourceLog m M Jalloc Ptest`:
--   1. $\sigma_j \le 1$ for all $j$, and $\xi \le 1$;
--   2. $|\sigma_j| \le \exp\bigl(-\mathrm{fixedPathSlicedPerturbationLog}(D^\ast,\ D^\ast + L_s + 4,\ \mathrm{cost} + 1,\ 2L_s + (E_{\mathrm{compare}} + 4) + 14,\ m)\bigr)$ for all $j$;
--   3. $\xi \le \exp\bigl(-(2L_s + (E_{\mathrm{compare}} + 4) + 14)\bigr)$;
--   4. `preparedSlicedForecastCommonFloor 0 childLog cost F` $\le S$, where $F =$ `preparedSlicedForecastComparisonFloorLog m M nX Jalloc ((nX + m M) + Σprep) Pdim cost pRadius gainLog Qstride Ptest (2 Ptest) Ecompare`;
--   5. for all $i$, $\exp\bigl(\mathrm{forecastJointGridAmbientLog}((n_X + mM) + \Sigma_{\mathrm{prep}},\ G_{\log},\ E_{\mathrm{compare}} + 4,\ 2P_{\mathrm{test}},\ \mathrm{gainLog} + n_X + 8)\bigr) \le N_i$, where $G_{\log} =$ `preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpoint_source_bounds_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpoint_source_bounds` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeEndpointSourceBounds.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B150` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeEndpointSourceBounds.lean (declaration OAI.Erdos3.VectorPolynomial.preparedRelativeEndpoint_source_bounds)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B150

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedRelativeEndpoint_source_bounds_s2
    {X J : Type} {m : ℕ} (prep : RankPreparationFamily X J m)
    (M nX Jalloc : ℕ) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (σ : Fin m → ℝ) (ξ : ℝ) (S : ℕ) (N : Fin nX → ℕ)
    {T K seed childLog Pdim cost pRadius gainLog Qstride Ptest Ecompare : ℝ}
    (hK : 0 ≤ K) (hT : 1 ≤ T) (hm : (m : ℝ) ≤ T)
    (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ T)
    (hD : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ T)
    (hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ T)
    (hpcap : preparedSlicedForecastPrimitiveCap ≤ T)
    (hPbad : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ T)
    (hcost : 0 ≤ cost) (hcostOne : cost + 1 ≤ T)
    (hTest : Ptest ∈ Set.Icc 0 T) (hCompare : Ecompare ∈ Set.Icc 0 T)
    (hRadius : pRadius ≤ T) (hTau : gainLog + (nX : ℝ) + 8 ≤ T)
    (hSigmaLog : preparedRelativeEndpointSigmaLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare cost m ≤ K)
    (hCoarseLog : preparedRelativeEndpointCoarseLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare ≤ K)
    (hFloorLog : (T + 10) ^ (2 * m + 20) ≤ K)
    (hσzero : ∀ j, 0 ≤ σ j) (hσK : ∀ j, σ j ≤ Real.exp (-K))
    (hξK : ξ ≤ Real.exp (-K))
    (hS : preparedRelativeEndpointMinimumScale seed 0 childLog cost
      ((T + 10) ^ (2 * m + 20)) ≤ S)
    (hN : ∀ i, Real.exp K ≤ (N i : ℝ)) :
    (∀ j, σ j ≤ 1) ∧ ξ ≤ 1 ∧
    (∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) +
        preparedSlicedForecastSourceLog m M Jalloc Ptest + 4) (cost + 1)
      (2 * preparedSlicedForecastSourceLog m M Jalloc Ptest + (Ecompare + 4) + 14) m)) ∧
    ξ ≤ Real.exp (-(2 * preparedSlicedForecastSourceLog m M Jalloc Ptest + (Ecompare + 4) + 14)) ∧
    preparedSlicedForecastCommonFloor 0 childLog cost
      (preparedSlicedForecastComparisonFloorLog m M nX Jalloc
        ((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j))
        Pdim cost pRadius gainLog Qstride Ptest (2 * Ptest) Ecompare) ≤ S ∧
    (∀ i, Real.exp (forecastJointGridAmbientLog
      ((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j))
      (preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest)
      (Ecompare + 4) (2 * Ptest) (gainLog + (nX : ℝ) + 8)) ≤ (N i : ℝ)) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
