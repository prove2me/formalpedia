-- Prove2me | Theorems.Thm_HardCoreLocalSampling_Local_uniform_root_margin
-- name    : HardCoreLocalSampling.Local.uniform_root_margin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:59.916001+00:00
-- url     : https://prove2.me/theorems/731239b0-8e97-45e3-959e-76b4b8e678c8
-- title:
--   Lemma 12 — Uniform root margin
-- statement:
--   With $m=\min\{1/(1+\lambda),\lambda/((1+\lambda)^\Delta+\lambda),1/4\}$, one has $m\le p_0\le1-m$, where $p_0=P_d(c_{s_1},\dots,c_{s_d})$ at the root's child centers, $d\le\Delta$.
--
--   This margin keeps the second branch of the root construction a valid probability. The root's arity may be $\Delta$; no contraction is asserted at the root.
--
--   Differences from the source:
--   - generalization: the centers of Lemma 9 → any centers in [0,U]; reason: the proof uses only this interval, which Lemma 9 asserts for its centers
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Lemma 12, eq. (10), printed p.10 (PDF p.11)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Params

namespace HardCoreLocalSampling.Local

/-- Thomas Chen, STOC 2027 submission #462, Lemma 12, printed p.10 (PDF p.11), with `m` from
(10): `m ≤ p_0 ≤ 1 - m` for `p_0 = P_d(c)`, for every arity `d ≤ Δ` and centers in `[0,U]`. -/
theorem uniform_root_margin (Delta : ℕ) (lam : ℚ) (hS : Standing Delta lam) (d : ℕ)
    (hd : d ≤ Delta) (c : Fin d → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hcU : ∀ i, c i ≤ Umsg (lam : ℝ)) :
    (mParam Delta lam : ℝ) ≤ Pd (lam : ℝ) c ∧ Pd (lam : ℝ) c ≤ 1 - (mParam Delta lam : ℝ) := by sorry

end HardCoreLocalSampling.Local
