-- Prove2me | Theorems.Thm_NearLinIsing_lemma_4_3
-- name    : NearLinIsing.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:43.03021+00:00
-- url     : https://prove2.me/theorems/cc5e95c0-a1e5-48c9-98d9-ce96679042ad
-- title:
--   Lemma 4.3 — cycle spectrum and activity bounds
-- statement:
--   Under the hypotheses of Proposition 4.1, the cycle polymer model of the port graph $H$ satisfies
--
--   $$\lambda_{\min}(AW)\ge-\frac56,\qquad\sum_Cw_Ce^{D(C)/2}\le2\sqrt e\,|E(H)|,\qquad\sum_C|C|\,w_C\le|E(H)|.\tag{14}$$
--
--   These are the hypotheses of the lower-spectrum branch of Theorem 1.5 with $\eta=1/2$, $\delta=1/6$ and $N=10m$, and the strict margin holds even at criticality $(\Delta-1)r=1$.
--
--   Differences from the source:
--   - encoding: the cycle representation supplied by Proposition 4.1 → the cycle model of `portGraph G r` under the hypotheses of Proposition 4.1; reason: the construction of pp. 18–19
--   - encoding: λmin(AW) ≥ −5/6 → the Rayleigh bound for W^{1/2}AW^{1/2} with the diagonal, on finitely supported vectors; reason: §2.4 fixes this meaning; the type space is finite here
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Lemma 4.3, Eq. (14), p. 20

import Mathlib
import Definitions.Def_NearLinIsing_buildPort

namespace NearLinIsing

/-- **Lemma 4.3** (Cycle spectrum and activity bounds), p. 20, display (14).

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Lemma 4.3, Eq. (14), p. 20.

Under the hypotheses of Proposition 4.1 (`G` well formed, maximum degree at most `Δ ≥ 3`, `r > 0`,
`(Δ − 1) r ≤ 1`), the cycle polymer model of the port graph `H = portGraph G r` satisfies
`λmin(AW) ≥ −5/6`, `∑_C w_C e^{D(C)/2} ≤ 2√e |E(H)|` and `∑_C |C| w_C ≤ |E(H)|`.

**Formalization Note.** `λmin(AW) ≥ −5/6` is the Rayleigh bound for `W^{1/2} A W^{1/2}` with the
diagonal included (reading R7). The type space of cycles is finite, so the sums are finite. -/
theorem lemma_4_3 (Δ : ℕ) (hΔ : 3 ≤ Δ) (G : IncGraph) (hG : G.WellFormed)
    (hdeg : G.MaxDegLe Δ) (r : ℝ) (hr : 0 < r) (hΔr : ((Δ : ℝ) - 1) * r ≤ 1) :
    (portGraph G r).cycleModel.LambdaMinGe (-5 / 6) ∧
    ∑' C : (portGraph G r).Cyc,
        (portGraph G r).cycleModel.w C * Real.exp ((portGraph G r).cycleModel.D C / 2) ≤
      2 * Real.sqrt (Real.exp 1) * (portGraph G r).ne ∧
    ∑' C : (portGraph G r).Cyc, (C.1.card : ℝ) * (portGraph G r).cycleModel.w C ≤
      (portGraph G r).ne := by sorry

end NearLinIsing
