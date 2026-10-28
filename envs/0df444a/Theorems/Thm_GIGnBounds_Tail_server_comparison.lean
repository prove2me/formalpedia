-- Prove2me | Theorems.Thm_GIGnBounds_Tail_server_comparison
-- name    : GIGnBounds.Tail.server_comparison
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-25T00:35:40.885314+00:00
-- url     : https://prove2.me/theorems/50d6f0f0-11e1-47d4-afa6-66f0cd17fa6d
-- title:
--   Eq. (comparesspd1), pp. 36–37 — the n-server queue with n′ busy servers is dominated by the n′-server queue
-- statement:
--   Fix integers $1\le n'\le n$, an inter-arrival law $A$ and a service-time law $S$ (nonnegative, with finite positive means), and write $R(X)$ for the equilibrium (stationary-excess) law of $X$.
--
--   1. Let $\mathcal Q^{n'}_{\mathrm{res}}$ be the FCFS $GI/GI/n'$ queue in which the time until the first arrival is distributed as $R(A)$ and all $n'$ servers are initially busy, with i.i.d. residual service times distributed as $R(S)$, independent of the arrival process. Let $Q^{n'}_{\mathrm{res}}(t)$ be its number in system at time $t$.
--   2. Let $\mathcal Q^{n,n'}_{\mathrm{res}}$ be the FCFS $GI/GI/n$ queue with the same inter-arrival and service laws, first arrival distributed as $R(A)$, exactly $n'$ jobs initially in service with i.i.d. residual service times distributed as $R(S)$, and the other $n-n'$ servers initially empty. Let $Q^{n,n'}_{\mathrm{res}}(t)$ be its number in system at time $t$.
--
--   Then for all $t\ge0$ and all $z$,
--   $$\mathbb P\big(Q^{n,n'}_{\mathrm{res}}(t)\ge z\big)\le\mathbb P\big(Q^{n'}_{\mathrm{res}}(t)\ge z\big).$$
--
--   This is the distributional form of the classical monotonicity of FCFS multi-server queues in the number of servers (Berger and Whitt 1992, Theorem 1; Whitt 1981): adding idle servers can only decrease the number in system. Li and Goldberg combine it with Lemma 14 to prove Lemma 7, which drives their bounds on the probability of delay.
--
--   **Formalization Note.** Both queues are given by the Kiefer–Wolfowitz workload recursion of the setting file, with the product law `queueMeasure`. The initial law of $\mathcal Q^{n,n'}_{\mathrm{res}}$ puts $R(S)$ on the first $n'$ residual coordinates and a Dirac mass at $0$ on the remaining $n-n'$, and that of $\mathcal Q^{n'}_{\mathrm{res}}$ is `resInit n'`. Probabilities are `Measure.real` of the events $\{z\le Q(t)\}$, with $z$ real.
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, Section 'Proof of Lemma 7' (pp. 36–37), display (comparesspd1), citing Berger and Whitt (1992) Theorem 1 and Whitt (1981)

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

theorem server_comparison (n n' : ℕ) (hn' : 1 ≤ n') (hnn' : n' ≤ n) (μA μS : Measure ℝ)
    [IsProbabilityMeasure μA] [IsProbabilityMeasure μS] (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (t z : ℝ) (ht : 0 ≤ t) :
    (queueMeasure n μA μS ((eqLaw μA).prod
        (Measure.pi (fun i : Fin n => if (i : ℕ) < n' then eqLaw μS else Measure.dirac 0)))).real
        {ω | z ≤ (queueLength ω t : ℝ)} ≤
      (queueMeasure n' μA μS (resInit n' μA μS)).real {ω | z ≤ (queueLength ω t : ℝ)} := by sorry

end GIGnBounds.Tail
