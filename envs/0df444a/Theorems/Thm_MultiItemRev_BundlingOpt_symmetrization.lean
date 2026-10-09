-- Prove2me | Theorems.Thm_MultiItemRev_BundlingOpt_symmetrization
-- name    : MultiItemRev.BundlingOpt.symmetrization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:54.162553+00:00
-- url     : https://prove2.me/theorems/11a5017a-bf86-403b-86e5-e0e9dc8a44e6
-- title:
--   Symmetrization, p. 32 — for i.i.d. goods, µ̄ is IC, IR, NPT, symmetric and has the revenue of µ
-- statement:
--   Let $Y, Z$ be i.i.d. one-good valuations with law $\nu$ on $\mathbb{R}_+$, and let $\mu = (q,s)$ be an admissible two-good mechanism satisfying NPT. Its symmetrization $\bar\mu = (\bar q, \bar s)$,
--   $$\bar q_1(y,z) = \bar q_2(z,y) = \tfrac12\bigl(q_1(y,z) + q_2(z,y)\bigr), \qquad \bar s(y,z) = \tfrac12\bigl(s(y,z) + s(z,y)\bigr),$$
--   is admissible, satisfies NPT, is symmetric, and yields the same revenue:
--   $$\mathbb{E}[\bar s(Y,Z)] = \mathbb{E}[s(Y,Z)].$$
--
--   Consequently one may assume without loss of generality that a mechanism for two i.i.d. goods is symmetric, as the proof of Theorem 16 does.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 32, Appendix A.1, proof of Theorem B (symmetrization); invoked on p. 44

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_MultiItemRev_BundlingOpt_Bundling
open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.BundlingOpt

theorem symmetrization (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (M : Mechanism (Fin 2))
    (hM : IsAdmissible M ∧ IsNPT M) :
    IsAdmissible (symmetrize M) ∧ IsNPT (symmetrize M) ∧ IsSymmetric (symmetrize M) ∧
      expRevenue (Measure.pi (fun _ : Fin 2 => ν)) (symmetrize M) =
        expRevenue (Measure.pi (fun _ : Fin 2 => ν)) M := by sorry

end MultiItemRev.BundlingOpt
