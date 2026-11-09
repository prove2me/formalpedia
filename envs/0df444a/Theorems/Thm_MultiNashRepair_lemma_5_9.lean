-- Prove2me | Theorems.Thm_MultiNashRepair_lemma_5_9
-- name    : MultiNashRepair.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:29:55.968638+00:00
-- url     : https://prove2.me/theorems/d2708a8e-aba2-4e3b-a2dd-2d1cceba8af5
-- title:
--   Lemma 5.9 — the scalar value $U(f)=\min_{0\le H\le f}K_f(H)$ in closed form
-- statement:
--   For $0<f<1$ the minimum $U(f)=\min_{0\le H\le f}K_f(H)$ is attained, and
--   $$U(f)=\begin{cases}1+f, & 0<f\le\frac1{\sqrt3},\\[2pt] 5-4f-\frac1f+2(1-f)\sqrt{4-\frac2f}, & \frac1{\sqrt3}\le f\le\frac23,\\[2pt] \frac1f, & \frac23\le f<1.\end{cases}\qquad(5.42)$$
--
--   The closed form makes the choice of the activation fraction $f_0$ in (5.1) an effective search, which makes the threshold of Theorem 1.1 computable.
--
--   Differences from the source:
--   - encoding: $U(f)=\min_{0\le H\le f}K_f(H)$ → $U f$ as the infimum, plus the clause that it is the least element of $K_f([0,f])$; reason: the paper writes min, so attainment is asserted
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Lemma 5.9, (5.42), p.36

import Mathlib
import Definitions.Def_MultiNashRepair_ScalarCertificate

namespace MultiNashRepair

/-- **Lemma 5.9 (The Value for a Fixed Activation Parameter)** (Tang, Ding, Fang,
arXiv:2611.06076, Lemma 5.9, (5.42), p.36).

For `0 < f < 1` the minimum `U(f) = min_{0≤H≤f} K_f(H)` is attained, and
`U(f) = 1 + f` for `0 < f ≤ 1/√3`,
`U(f) = 5 − 4f − 1/f + 2(1 − f)√(4 − 2/f)` for `1/√3 ≤ f ≤ 2/3`,
`U(f) = 1/f` for `2/3 ≤ f < 1`. -/
theorem lemma_5_9 :
    (∀ f : ℝ, 0 < f → f < 1 → IsLeast (Kf f '' Set.Icc 0 f) (U f)) ∧
    (∀ f : ℝ, 0 < f → f ≤ 1 / Real.sqrt 3 → U f = 1 + f) ∧
    (∀ f : ℝ, 1 / Real.sqrt 3 ≤ f → f ≤ 2 / 3 →
      U f = 5 - 4 * f - 1 / f + 2 * (1 - f) * Real.sqrt (4 - 2 / f)) ∧
    (∀ f : ℝ, 2 / 3 ≤ f → f < 1 → U f = 1 / f) := by sorry

end MultiNashRepair
