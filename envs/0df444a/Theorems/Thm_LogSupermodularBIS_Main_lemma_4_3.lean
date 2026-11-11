-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_lemma_4_3
-- name    : LogSupermodularBIS.Main.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:46.650668+00:00
-- url     : https://prove2.me/theorems/c5722cbe-f233-4e21-b11d-8823a7d74d79
-- title:
--   Lemma 4.3 — the penalized objective is concave, sound for every candidate and Lipschitz
-- statement:
--   Let $W$ satisfy the assumptions of Theorem 1.2 ($d\ge2$, $B\ge1$, positive rational values of bit length at most $B$) and be log-supermodular. Let $v$ be a node whose residual has $k=d-|v|\ge1$ free coordinates, $\Phi=\Phi_v$, $\Lambda=2B$, and $m$, $G_0$ as in (4.1). The objective $J_v$ of (4.4) is concave on the space of candidates. Every candidate $u$ satisfies $J_v(u)\le\log Z_\Phi$, and any two candidates satisfy
--   $$|J_v(u)-J_v(u')|\le G_0\sum_iE|u_i-u'_i|.$$
--
--   Differences from the source: none.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 21 (PDF 22), Lemma 4.3

import Definitions.Def_LogSupermodularBIS_Main_Algorithms
import Definitions.Def_LogSupermodularBIS_Main_Interaction

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Lemma 4.3 (Soundness for every candidate), p. 21, at a node `v` with `k = d − |v| ≥ 1` free
coordinates, `Φ = Φ_v`, `m` and `G_0` of (4.1), `Λ = 2B`. -/
theorem lemma_4_3 {d : ℕ} (W : (Fin d → Bool) → ℚ) (B : ℕ) (hW : StandingWeight W B)
    (hlsm : LogSupermodular W) (v : List Bool) (hv : v.length < d) :
    ConcaveOn ℝ (candidates (d - v.length) (numBins d))
        (penalizedObjective (numBins d) (paramLambda B) (residualPotential W v)) ∧
    (∀ u ∈ candidates (d - v.length) (numBins d),
      penalizedObjective (numBins d) (paramLambda B) (residualPotential W v) u ≤
        Real.log (potentialPartition (residualPotential W v))) ∧
    ∀ u ∈ candidates (d - v.length) (numBins d), ∀ u' ∈ candidates (d - v.length) (numBins d),
      |penalizedObjective (numBins d) (paramLambda B) (residualPotential W v) u -
          penalizedObjective (numBins d) (paramLambda B) (residualPotential W v) u'| ≤
        paramG0 d B * ∑ i, binExpect fun y => |u i y - u' i y| := by sorry

end LogSupermodularBIS.Main
