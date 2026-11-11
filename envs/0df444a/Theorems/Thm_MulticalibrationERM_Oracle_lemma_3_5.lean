-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_lemma_3_5
-- name    : MulticalibrationERM.Oracle.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:50:19.529981+00:00
-- url     : https://prove2.me/theorems/b9b8b488-5479-400f-a8a3-d129f123bebc
-- title:
--   Lemma 3.5 — adjacent support costs at most 1/(2K)
-- statement:
--   If $P\in\Delta(\Lambda)$ has adjacent support and mean $\mu$, then $\sum_vP(v)|v-\mu|\le1/(2K)$. Consequently, for every $y\in[0,1]$ and $h\in\{-1,+1\}$,
--   $$\sum_{v\in\Lambda}\big|hP(v)(v-y)-hP(v)(\mu-y)\big|\le\frac1{2K}.$$
--
--   Differences from the source:
--   - encoding: grid values v ∈ Λ → grid indices i ∈ Fin (K + 1) with value i/K; reason: relabelling
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), p. 18, Lemma 3.5

import Mathlib
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_Forecast

namespace MulticalibrationERM.Oracle

/-- Lemma 3.5 (p. 18): a distribution `P` on the grid with adjacent support and mean `µ` has
`∑_v P(v) |v − µ| ≤ 1/(2K)`; consequently, for every `y ∈ [0, 1]` and `h ∈ {−1, +1}`,
`∑_v |h P(v)(v − y) − h P(v)(µ − y)| ≤ 1/(2K)`. -/
theorem lemma_3_5 (K : ℕ) (hK : 1 ≤ K) (P : Fin (K + 1) → ℝ) (hP : IsDist P)
    (hadj : AdjSupport P) :
    ∑ v, P v * |gv K v - gridMean P| ≤ 1 / (2 * (K : ℝ)) ∧
    ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ h : ℝ, (h = 1 ∨ h = -1) →
      ∑ v, |h * P v * (gv K v - y) - h * P v * (gridMean P - y)| ≤ 1 / (2 * (K : ℝ)) := by sorry

end MulticalibrationERM.Oracle
