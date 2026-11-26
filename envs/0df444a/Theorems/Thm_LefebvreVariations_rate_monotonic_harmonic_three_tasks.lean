-- Prove2me | Theorems.Thm_LefebvreVariations_rate_monotonic_harmonic_three_tasks
-- name    : LefebvreVariations.rate_monotonic_harmonic_three_tasks
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:37:13.912283+00:00
-- url     : https://prove2.me/theorems/ed216aae-ecd9-576a-92bc-b2ecd2585ccf
-- title:
--   Lefebvre's variations, No. 193 — on a theme by Liu and Layland: rate-monotonic scheduling of three tasks with harmonic periods meets every deadline up to utilization 1
-- statement:
--   Let $C_i,T_i$ ($i=0,1,2$) be positive integers with $C_i\le T_i$ and $T_0\mid T_1\mid T_2$, and suppose
--   $$
--   \sum_{i=0}^{2}\frac{C_i}{T_i}\ \le\ 1 .
--   $$
--   Then in the rate-monotonic schedule of the three periodic tasks, every job meets its deadline:
--   $$
--   \#\{\,s<(k+1)T_i : \text{task } i \text{ runs in slot } s\,\}\ \ge\ (k+1)\,C_i\qquad\text{for all } i\in\{0,1,2\},\ k\ge 0 .
--   $$
--
--   For general periods the Liu–Layland guarantee for three tasks stops at $3(2^{1/3}-1)\approx 0.780$; for a harmonic chain of periods the threshold rises to $1$. The platform's open problem is the general-$n$ Liu–Layland bound; this is the harmonic three-task companion in the same model.
--
--   Time is divided into unit slots. Task $i$ releases its $k$-th job at time $kT_i$, with deadline $(k+1)T_i$ and $C_i$ slots of work; in every slot the processor runs the pending task with the shortest period (ties broken by the smaller index), or idles if none is pending. This is the rate-monotonic schedule of Liu and Layland in discrete time.
--
--   **Formalization Note** The tasks are `Fin 3`, with `C T : Fin 3 → ℕ`, `1 ≤ C i ≤ T i`. The schedule `σ : ℕ → Option (Fin 3)` is characterised by the hypothesis `hσ`: `σ t = some i` iff task `i` has pending work at `t` (its service so far is below `C i` times the number of jobs released by `t`, which is `⌊t / T i⌋ + 1`) and no higher-priority task has pending work. This determines `σ` uniquely by recursion on `t`. The conclusion says that by time `(k + 1) * T i` task `i` has received at least `(k + 1) * C i` slots. The extra hypotheses state that the periods divide one another.
--
--   **Why this is a variation.** A companion to the open platform problem LiuLayland1973.rate_monotonic_utilization_bound: same schedule model (restated verbatim, not imported), with the hypothesis 'utilization <= n(2^{1/n} - 1)' replaced by 'harmonic chain of periods and utilization <= 1', at three tasks. It is not a special case of the parent's statement (its threshold is larger) but addresses the same question on a structured family.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Model and general bound: C. L. Liu and J. W. Layland, Journal of the ACM 20(1) (1973), 46-61 (cited from memory). The harmonic-period case with utilization bound 1 is usually credited to T.-W. Kuo and A. K. Mok, Load adjustment in adaptive real-time systems, RTSS 1991 (bibliographic data confirmed by search; the single-harmonic-chain bound 1 is the K = 1 case of the K(2^{1/K} - 1) bound for K harmonic chains as reported in later work by Chen, Mok and Kuo; exact theorem number not checked). Checked by exhaustive simulation over one hyperperiod for T_0 <= 8, T_1 = a T_0, T_2 = b T_1 with a <= 4, b <= 3 and all C_i <= T_i with utilization <= 1 (27720 instances, no missed deadline).

import Mathlib

namespace LefebvreVariations

/-- Rate-monotonic scheduling with three harmonic tasks, in the discrete-time model of the Liu–Layland
platform problem: tasks `Fin 3`, task `i` runs `C i` unit slots every `T i`, releasing its `k`-th
job at `k * T i` with deadline `(k + 1) * T i`; `σ t` is the highest-priority (shortest period,
ties by index) task with pending work, or idle. Harmonic chain of periods (`T 0 ∣ T 1 ∣ T 2`): utilization at most `1` suffices.
Source: C. L. Liu and J. W. Layland, *Scheduling algorithms for multiprogramming in a hard-real-time
environment*, J. ACM 20 (1973) The harmonic case beating the general bound is a known later refinement (Kuo and Mok 1991, cited from memory). Checked by simulation for `T 0 ≤ 8`, ratios up to 4 and 3. -/
theorem rate_monotonic_harmonic_three_tasks (C T : Fin 3 → ℕ)
    (hC : ∀ i, 1 ≤ C i) (hCT : ∀ i, C i ≤ T i) (hdvd₁ : T 0 ∣ T 1) (hdvd₂ : T 1 ∣ T 2)
    (hU : ∑ i, (C i : ℝ) / (T i : ℝ) ≤ 1)
    (σ : ℕ → Option (Fin 3))
    (hσ : ∀ (t : ℕ) (i : Fin 3), σ t = some i ↔
      (((Finset.range t).filter (fun s => σ s = some i)).card <
          C i * ((Finset.range (t + 1)).filter (fun k => k * T i ≤ t)).card) ∧
      ∀ j : Fin 3, (T j < T i ∨ (T j = T i ∧ j < i)) →
        C j * ((Finset.range (t + 1)).filter (fun k => k * T j ≤ t)).card ≤
          ((Finset.range t).filter (fun s => σ s = some j)).card)
    (i : Fin 3) (k : ℕ) :
    (k + 1) * C i ≤
      ((Finset.range ((k + 1) * T i)).filter (fun s => σ s = some i)).card := by
  sorry

end LefebvreVariations
