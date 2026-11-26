-- Prove2me | Theorems.Thm_LefebvreVariations_rate_monotonic_harmonic_two_tasks
-- name    : LefebvreVariations.rate_monotonic_harmonic_two_tasks
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:36:59.646632+00:00
-- url     : https://prove2.me/theorems/8b0d9df7-190f-4767-83f2-a0a3166766bd
-- title:
--   Lefebvre's variations, No. 191 — on a theme by Liu and Layland: rate-monotonic scheduling of two tasks with harmonic periods meets every deadline up to utilization 1
-- statement:
--   Let $C_0,C_1,T_0,T_1$ be positive integers with $C_i\le T_i$ and $T_0\mid T_1$, and suppose
--   $$
--   \frac{C_0}{T_0}+\frac{C_1}{T_1}\ \le\ 1 .
--   $$
--   Then in the rate-monotonic schedule of the two periodic tasks, every job meets its deadline:
--   $$
--   \#\{\,s<(k+1)T_i : \text{task } i \text{ runs in slot } s\,\}\ \ge\ (k+1)\,C_i\qquad\text{for all } i\in\{0,1\},\ k\ge 0 .
--   $$
--
--   For general periods the Liu–Layland guarantee stops at the utilization $2(\sqrt2-1)\approx 0.828$; when the periods are harmonic the threshold rises to $1$. The platform's open problem is the general-$n$ Liu–Layland bound; this is the harmonic two-task companion in the same model.
--
--   Time is divided into unit slots. Task $i$ releases its $k$-th job at time $kT_i$, with deadline $(k+1)T_i$ and $C_i$ slots of work; in every slot the processor runs the pending task with the shortest period (ties broken by the smaller index), or idles if none is pending. This is the rate-monotonic schedule of Liu and Layland in discrete time.
--
--   **Formalization Note** The tasks are `Fin 2`, with `C T : Fin 2 → ℕ`, `1 ≤ C i ≤ T i`. The schedule `σ : ℕ → Option (Fin 2)` is characterised by the hypothesis `hσ`: `σ t = some i` iff task `i` has pending work at `t` (its service so far is below `C i` times the number of jobs released by `t`, which is `⌊t / T i⌋ + 1`) and no higher-priority task has pending work. This determines `σ` uniquely by recursion on `t`. The conclusion says that by time `(k + 1) * T i` task `i` has received at least `(k + 1) * C i` slots. The extra hypotheses state that the periods divide one another.
--
--   **Why this is a variation.** A companion to the open platform problem LiuLayland1973.rate_monotonic_utilization_bound: same schedule model (restated verbatim, not imported), but the hypothesis 'utilization <= n(2^{1/n} - 1)' is replaced by 'harmonic periods and utilization <= 1', at two tasks. It is therefore not a special case of the parent's statement (its threshold is larger), but it answers the same question, when RM meets all deadlines, on a structured family.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Model and general bound: C. L. Liu and J. W. Layland, Journal of the ACM 20(1) (1973), 46-61 (cited from memory). The harmonic-period case with utilization bound 1 is usually credited to T.-W. Kuo and A. K. Mok, Load adjustment in adaptive real-time systems, RTSS 1991 (bibliographic data confirmed by search; the single-harmonic-chain bound 1 is the K = 1 case of the K(2^{1/K} - 1) bound for K harmonic chains as reported in later work by Chen, Mok and Kuo; exact theorem number not checked). Checked by exhaustive simulation over one hyperperiod for T_0 <= 20, T_1 = m T_0 with m <= 10, and all C_i <= T_i with utilization <= 1 (73150 instances, no missed deadline).

import Mathlib

namespace LefebvreVariations

/-- Rate-monotonic scheduling with two harmonic tasks, in the discrete-time model of the Liu–Layland
platform problem: tasks `Fin 2`, task `i` runs `C i` unit slots every `T i`, releasing its `k`-th
job at `k * T i` with deadline `(k + 1) * T i`; `σ t` is the highest-priority (shortest period,
ties by index) task with pending work, or idle. Harmonic periods (`T 0 ∣ T 1`): utilization at most `1` suffices.
Source: C. L. Liu and J. W. Layland, *Scheduling algorithms for multiprogramming in a hard-real-time
environment*, J. ACM 20 (1973) The harmonic case beating the general bound is a known later refinement (Kuo and Mok 1991, cited from memory). Checked by simulation for `T 0 ≤ 20`, `T 1 ≤ 10 · T 0`. -/
theorem rate_monotonic_harmonic_two_tasks (C T : Fin 2 → ℕ)
    (hC : ∀ i, 1 ≤ C i) (hCT : ∀ i, C i ≤ T i) (hdvd : T 0 ∣ T 1)
    (hU : ∑ i, (C i : ℝ) / (T i : ℝ) ≤ 1)
    (σ : ℕ → Option (Fin 2))
    (hσ : ∀ (t : ℕ) (i : Fin 2), σ t = some i ↔
      (((Finset.range t).filter (fun s => σ s = some i)).card <
          C i * ((Finset.range (t + 1)).filter (fun k => k * T i ≤ t)).card) ∧
      ∀ j : Fin 2, (T j < T i ∨ (T j = T i ∧ j < i)) →
        C j * ((Finset.range (t + 1)).filter (fun k => k * T j ≤ t)).card ≤
          ((Finset.range t).filter (fun s => σ s = some j)).card)
    (i : Fin 2) (k : ℕ) :
    (k + 1) * C i ≤
      ((Finset.range ((k + 1) * T i)).filter (fun s => σ s = some i)).card := by
  sorry

end LefebvreVariations
