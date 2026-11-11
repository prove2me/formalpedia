-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_lemma_4_4
-- name    : LogSupermodularBIS.Main.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:52.74508+00:00
-- url     : https://prove2.me/theorems/9a32caf6-880a-487a-8417-23ba8d7f3e26
-- title:
--   Lemma 4.4 — a low-degree Walsh candidate
-- statement:
--   In the setting of Lemma 4.3, let $0\le D\le d$ and $b^*\ge0$, and suppose the node $v$ admits a guide $g$ satisfying (4.2). There is a candidate $u^*$ such that each row $u^*_i$ is a linear combination, with coefficients in $[-1,1]$, of the Walsh characters whose supports lie in $\{1,\dots,i\}$ and have at most $D$ elements, and
--   $$J_v(u^*)\ge\log Z_\Phi-b^*-\frac1{32}.$$
--
--   Differences from the source:
--   - encoding: coordinates and rows 1, …, d → Fin d, indices 0, …, d−1; reason: index shift only
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 22 (PDF 23), Lemma 4.4

import Definitions.Def_LogSupermodularBIS_Main_Algorithms
import Definitions.Def_LogSupermodularBIS_Main_Interaction

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Lemma 4.4 (Low-degree candidate), p. 22, at a node `v` with `k = d − |v| ≥ 1` free
coordinates satisfying the witness assumption (4.2). -/
theorem lemma_4_4 {d : ℕ} (W : (Fin d → Bool) → ℚ) (B : ℕ) (hW : StandingWeight W B)
    (hlsm : LogSupermodular W) (D : ℕ) (hD : D ≤ d) (bstar : ℝ) (hb : 0 ≤ bstar)
    (v : List Bool) (hv : v.length < d) (hwit : WitnessAt W B D bstar v) :
    ∃ θ : Fin (d - v.length) → (Fin (d - v.length) → Fin (numBins d)) → ℝ,
      (∀ i β, θ i β ∈ Set.Icc (-1 : ℝ) 1) ∧
      (fun i y => ∑ β ∈ walshRowIndices D i, θ i β * walsh (paramS d) β y) ∈
        candidates (d - v.length) (numBins d) ∧
      Real.log (potentialPartition (residualPotential W v)) - bstar - 1 / 32 ≤
        penalizedObjective (numBins d) (paramLambda B) (residualPotential W v)
          (fun i y => ∑ β ∈ walshRowIndices D i, θ i β * walsh (paramS d) β y) := by sorry

end LogSupermodularBIS.Main
