-- Prove2me | Theorems.Thm_FracTruthSched_theorem_2
-- name    : FracTruthSched.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:30:48.928644+00:00
-- url     : https://prove2.me/theorems/cb345fff-1874-4b1a-84d8-32414fbb4fbf
-- title:
--   Theorem 2 — every truthful fractional mechanism family has ratio at least $(n+1)/2$ against the integral optimum
-- statement:
--   Consider scheduling on $n\ge1$ unrelated machines. Let $(R_m)_{m\ge1}$ be any family of deterministic truthful fractional mechanisms on $n$ machines, one for every finite number $m$ of tasks, each feasible and truthful on all nonnegative inputs. Then for every $\delta>0$ there are $m$ and a nonnegative input $t$ with $m$ tasks and $\mathrm{Opt}(t)>0$ such that
--   $$\mathrm{Mech}_{R_m}(t)\ >\ \Big(\frac{n+1}{2}-\delta\Big)\mathrm{Opt}(t),$$
--   where $\mathrm{Opt}$ is the optimal **integral** makespan. In words: every deterministic truthful fractional mechanism has approximation ratio at least $(n+1)/2$, even against the optimal integral makespan, when arbitrary finite numbers of tasks are allowed (Theorem 1).
--
--   No continuity, task independence, anonymity or consistency between different task counts is assumed, and payments may have any sign. Together with the $(n+1)/2$-approximate fractional mechanism of Christodoulou, Koutsoupias and Kovács, this shows that $(n+1)/2$ is the optimal ratio of truthful fractional scheduling; by the reduction of §2.1 it also lower-bounds truthful-in-expectation randomized mechanisms.
--
--   Differences from the source:
--   - encoding: (R_m)_{m≥1}, one mechanism for every finite number of tasks → R : (m : ℕ) → FracMech n (Fin m); reason: the member at m = 0 is never used: the witness has Opt(t) > 0 and so m ≥ 1
--   - encoding: n unrelated machines → Fin n with [NeZero n]; reason: n ≥ 1
--   - encoding: a deterministic fractional mechanism on nonnegative inputs: x_ij(t) ∈ [0,1], Σ_i x_ij(t) = 1, payments P_i(t), truthfulness (1) for nonnegative true types, reports and opposing reports → FracMech n τ (total functions x, P on real matrices) with IsFeasibleOn and IsTruthfulOn imposed on the admissible inputs only (Nonneg, resp. IsGraphInput); values elsewhere are unconstrained; reason: Lean convention; the paper's mechanisms are exactly the restrictions of such pairs to the admissible inputs
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Theorem 2, p.6 (= Theorem 1, p.1, with the finite-witness clause)

import Mathlib
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_makespan
import Definitions.Def_FracTruthSched_opt

set_option autoImplicit false

namespace FracTruthSched

/-- **Theorem 2** (Anastasiadis et al., *Tight bounds for fractional and randomized truthful
scheduling*, arXiv:2611.06642v1, Theorem 2, p.6; its first sentence is Theorem 1, p.1). Every
deterministic truthful fractional mechanism for scheduling `n` unrelated machines has approximation
ratio at least `(n + 1)/2`, even against the optimal integral makespan, when arbitrary finite numbers
of tasks are allowed. More precisely, for every family `(R_m)_{m≥1}` of such mechanisms and every
`δ > 0`, there are `m` and an input `t` with `m` tasks and `Opt(t) > 0` such that
`Mech_{R_m}(t) > ((n + 1)/2 − δ) Opt(t)`.

**Formalization Note.** Machines are `Fin n` with `n ≥ 1` (`[NeZero n]`), tasks `Fin m`; the family is
`R : (m : ℕ) → FracMech n (Fin m)` (the member at `m = 0` is never used, since `Opt(t) > 0` forces
`m ≥ 1`). Each `R m` is feasible and truthful on nonnegative inputs; no continuity, task
independence, anonymity, consistency across `m` or sign of payments is assumed. `Opt` is the
*integral* optimum. -/
theorem theorem_2 {n : ℕ} [NeZero n] (R : (m : ℕ) → FracMech n (Fin m))
    (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (htruth : ∀ m, IsTruthfulOn Nonneg (R m))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t ∧ 0 < opt t ∧
      (((n : ℝ) + 1) / 2 - δ) * opt t < makespan (R m) t := by sorry

end FracTruthSched
