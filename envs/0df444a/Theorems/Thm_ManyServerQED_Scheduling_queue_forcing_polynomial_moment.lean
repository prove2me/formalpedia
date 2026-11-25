-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_forcing_polynomial_moment
-- name    : ManyServerQED.Scheduling.queue_forcing_polynomial_moment
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T19:36:51.637531+00:00
-- url     : https://prove2.me/theorems/5337075b-50c8-4440-a7a3-d42a55e65e09
-- title:
--   Polynomial moment estimate for the diffusion-scaled queue forcing
-- statement:
--   Let $W^n$ be the forcing path in the diffusion-scaled queue balance, comprising the scaled initial population, the centered arrival counts, the centered service and abandonment counts at their operational clocks, and the deterministic first-order rate correction. For work-conserving systems with diffusion-scaled initial population converging to $x$, the $m_U$-moment of the supremum of the $\ell^1$ norm of $W^n$ up to time $t$ is bounded by
--   $$c(1+\lVert x\rVert_1^m)(1+t^m)$$
--   for all sufficiently large $n$ and every $t\ge0$. The constants $c,m$ depend on the model and moment parameters. Combined with the deterministic state estimate, this gives the polynomial state-moment bound used for infinite-horizon discounted costs.
-- source:
--   Atar, Mandelbaum and Reiman, https://arxiv.org/pdf/math/0407058, proof of Lemma 3 §5.1, queue balance (15)–(16), and the primitive bounds of Lemma 2

import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_forcing_polynomial_moment
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] (M : SystemSequence Ω k)
    (mL mU : ℝ) (hA3 : M.Assumption3 mL mU) :
    ∃ (c : ℝ≥0) (m : ℕ), ∀ (x : Fin k → ℝ) (X0 : ℕ → Fin k → ℕ),
      Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x) →
      ∀ (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ),
      (∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n) ∧ IsWorkConserving n (X n) (Ψ n)) →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t : ℝ, 0 ≤ t →
      let W (ω : Ω) (s : ℝ) (i : Fin k) :=
        M.Xhat0 n (X0 n) i + M.Ahat n ω s i -
        M.Rhat n ω (queueTime (X n) (Ψ n) ω i s / n) i -
        M.Shat n ω (busyTime (Ψ n) ω i s / n) i +
        ((M.lamN n i - M.rho i * M.muN n i * n) / Real.sqrt n) * s
      (∫⁻ ω, (supDist (W ω) (fun _ => 0) t) ^ mU ∂M.P) ≤
        ENNReal.ofReal ((c : ℝ) * (1 + l1norm x ^ m) * (1 + t ^ m)) := by sorry
