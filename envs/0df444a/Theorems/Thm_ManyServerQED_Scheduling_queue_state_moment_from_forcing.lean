-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_state_moment_from_forcing
-- name    : ManyServerQED.Scheduling.queue_state_moment_from_forcing
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T18:32:32.13066+00:00
-- url     : https://prove2.me/theorems/c7616b36-cf30-4d1a-81ab-26094098f374
-- title:
--   Queue state moments bounded by moments of the centered primitive forcing
-- statement:
--   Let $X^n$ and $\Psi^n$ satisfy the controlled queue equations and work conservation. Let $W^n$ be the additive input in the centered balance equation. It consists of the scaled initial state, the centered arrivals, the centered service and abandonment counts evaluated at their clocks, and the deterministic input-rate correction. If $a>0$ bounds all service and abandonment rates, then for $p\ge 0$ and $T\ge 0$,
--   $$
--   E\|\widehat X^n(T)\|_1^p\le
--   \big(k(1+aT)^2\big)^p E\left[\left(\sup_{0\le s\le T}\|W^n(s)\|_1\right)^p\right].
--   $$
--   The expectation on the right is the lower integral of the $p$-th power of the supremum. The bound transfers primitive moment estimates to the state in the proof of Lemma 3.
-- source:
--   Atar, Mandelbaum and Reiman (2004), https://arxiv.org/abs/math/0407058, equation (13), work conservation (18), and the deterministic estimate in Lemma 3, pp. 32–33.

import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory Set
open scoped ENNReal

namespace ManyServerQED.Scheduling

open BellWilliams2001.ThresholdPolicy

theorem queue_state_moment_from_forcing {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k]
    (M : SystemSequence Ω k) (n : ℕ) (hn : 0 < n) (X0 : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hC : M.IsControlled n X0 X Ψ)
    (hWork : IsWorkConserving n X Ψ)
    (a : ℝ) (ha : 0 < a) (hμa : ∀ i, M.muN n i ≤ a) (hθa : ∀ i, M.thetaN n i ≤ a)
    (T : ℝ) (hT : 0 ≤ T) (p : ℝ) (hp : 0 ≤ p) :
    let W (ω : Ω) (t : ℝ) (i : Fin k) :=
      M.Xhat0 n X0 i + M.Ahat n ω t i -
      M.Rhat n ω (queueTime X Ψ ω i t / n) i -
      M.Shat n ω (busyTime Ψ ω i t / n) i +
      ((M.lamN n i - M.rho i * M.muN n i * n) / Real.sqrt n) * t
    (∫⁻ ω, ENNReal.ofReal (l1norm (M.Xhat n X ω T)) ^ p ∂M.P) ≤
      ENNReal.ofReal ((k : ℝ) * (1 + a * T) ^ 2) ^ p *
        ∫⁻ ω, (supDist (W ω) (fun _ => 0) T) ^ p ∂M.P := by sorry

end ManyServerQED.Scheduling
