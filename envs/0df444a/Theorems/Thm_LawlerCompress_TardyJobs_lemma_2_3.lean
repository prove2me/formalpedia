-- Prove2me | Theorems.Thm_LawlerCompress_TardyJobs_lemma_2_3
-- name    : LawlerCompress.TardyJobs.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:25:19.585457+00:00
-- url     : https://prove2.me/theorems/37a087d0-ec3d-44eb-a59d-a8c9ca71753f
-- title:
--   Lemma 2.3 — Total length of the canonical intervals
-- statement:
--   For every m≥1 there is a positive real constant K depending only on m such that every nonempty EDD instance on m machines satisfies
--
--   $$\sum_{j=1}^n|\bar C_j|=\sum_{p=1}^{d_{\max}}\sum_{t=p}^{d_{\max}}|\bar T_{p,t}|\le m d_{\max}^2(1+\ln d_{\max})\le Kd_{\max}^2(1+\ln d_{\max}).$$
--
--   The explicit coefficient m and exponent two are retained. The last comparison states the source's soft-O family bound with a constant chosen before the instance. This is the interval-size target used in the resource analysis.
--
--   **Formalization Note** All sums are finite; d_max≥1 follows from n≥1 and 1≤p_j≤d_j.
--
--   Differences from the source:
--   - encoding: jobs and machines numbered from one; positive integral data; a nonempty input with a maximum due date → Fin n jobs and Fin m machines, natural data in Instance, with m,n ≥ 1; reason: zero-based reindexing preserves every schedule and excludes only the undefined empty maximum
--   - encoding: the final comparison with Õ_m(d_max²) → a positive constant K after m and before the instance bounding the explicit m d²(1+ln d) expression; reason: this serializes the displayed asymptotic clause while retaining the preceding exact equality and constant
-- source:
--   Klaus Jansen, Björn Schumacher, Corinna Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), p. 5, Lemma 2.3

import Definitions.Def_LawlerCompress_TardyJobs_Canonical

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

theorem lemma_2_3 :
    ∀ m : ℕ, 1 ≤ m → ∃ K : ℝ, 0 < K ∧
    ∀ I : Instance m, 1 ≤ I.n → EDD I →
      (∑ j, (cbar I j).card) =
        (∑ p ∈ Finset.Icc 1 (dmax I), ∑ t ∈ Finset.Icc p (dmax I), (tbar I p t).card) ∧
      ((∑ j, (cbar I j).card) : ℝ) ≤
        (m : ℝ) * dmax I ^ 2 * (1 + Real.log (dmax I)) ∧
      (m : ℝ) * dmax I ^ 2 * (1 + Real.log (dmax I)) ≤
        K * dmax I ^ 2 * (1 + Real.log (dmax I)) := by sorry

end LawlerCompress.TardyJobs
