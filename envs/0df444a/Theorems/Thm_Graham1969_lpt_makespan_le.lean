-- Prove2me | Theorems.Thm_Graham1969_lpt_makespan_le
-- name    : Graham1969.lpt_makespan_le
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:37:05.568806+00:00
-- url     : https://prove2.me/theorems/38b20501-771b-40b0-8371-bbbdcdabb1d6
-- title:
--   Graham's LPT bound: $C_{\max}(\mathrm{LPT}) \le \left(\frac{4}{3} - \frac{1}{3m}\right)\mathrm{OPT}$ on $m$ identical machines
-- statement:
--   This is Graham's worst-case bound for the *longest processing time* (LPT) rule for scheduling independent jobs on identical parallel machines so as to minimize the makespan (the problem $P\,\|\,C_{\max}$).
--
--   Let $m \ge 1$ be the number of identical machines, and let jobs $1, \dots, n$ (with $n \ge 0$) have nonnegative real processing times listed in nonincreasing order,
--
--   $$p_1 \ge p_2 \ge \cdots \ge p_n \ge 0 .$$
--
--   An *assignment* is a map $\tau : \{1,\dots,n\} \to \{1,\dots,m\}$ sending each job to the machine that processes it. The *load* of machine $j$ under $\tau$ is $L_j(\tau) = \sum_{k \,:\, \tau(k) = j} p_k$, the *makespan* of $\tau$ is $C_{\max}(\tau) = \max_{1 \le j \le m} L_j(\tau)$, and the optimal makespan is
--
--   $$\mathrm{OPT} = \min_{\tau} C_{\max}(\tau),$$
--
--   the minimum being taken over all $m^n$ assignments.
--
--   An assignment $\sigma$ is an *LPT schedule* if it arises from list scheduling of the jobs in the order $1, 2, \dots, n$: each job $i$ is placed on a machine whose current load
--
--   $$\sum_{k < i,\ \sigma(k) = j} p_k$$
--
--   (the total processing time of the earlier jobs already placed on machine $j$) is minimal among all machines $j = 1, \dots, m$. Ties between equally loaded machines may be broken arbitrarily, and jobs of equal length may appear in any order. Then every LPT schedule $\sigma$ satisfies
--
--   $$C_{\max}(\sigma) \le \left(\frac{4}{3} - \frac{1}{3m}\right)\mathrm{OPT}.$$
--
--   This is the classical first example of the worst-case analysis of a greedy approximation algorithm. It sharpens Graham's earlier bound $2 - \frac{1}{m}$, valid for list scheduling in an arbitrary order, by exploiting the sorted order of the list; Graham also showed that the constant $\frac{4}{3} - \frac{1}{3m}$ is attained for every $m$.
--
--   **Formalization Note** Jobs are indexed by `Fin n` (job $i$ of the text is index $i-1$) and machines by `Fin m`; the processing times are a function `p : Fin n → ℝ` with `0 ≤ p i`, and the nonincreasing order is `Antitone p`. The LPT rule is the hypothesis that for every job $i$ and every machine $j$ the load of machine $\sigma(i)$ from the jobs before $i$ is at most the load of machine $j$ from the jobs before $i$. For independent jobs this is exactly Graham's list scheduling, in which a processor that becomes free takes the next job on the list, since the processor that becomes free first is a least-loaded one. The makespan is a `Finset.sup'` over the machines and $\mathrm{OPT}$ a `Finset.inf'` over all functions `Fin n → Fin m`; the hypothesis $m \ge 1$ (`hm : 0 < m`) supplies the nonemptiness witnesses. Graham states the bound as the ratio $\omega_L/\omega_0$ with $n$ processors; here it is stated multiplicatively, which also covers the degenerate case $\mathrm{OPT} = 0$. Jobs of length $0$ are allowed; they do not change any load.
-- source:
--   R. L. Graham, Bounds on multiprocessing timing anomalies, SIAM J. Appl. Math. 17(2) (1969), 416-429, Theorem 2 (independent tasks, list L in decreasing order of execution times on n processors: omega_L/omega_0 <= 4/3 - 1/(3n)); see also D. P. Williamson and D. B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press (2011), Section 2.3 (the longest processing time rule for scheduling jobs on identical parallel machines).

import Mathlib

namespace Graham1969

/-- Graham's LPT bound (Graham 1969, Theorem 2): on `m ≥ 1` identical machines, list scheduling
of jobs sorted by nonincreasing processing time (each job goes to a currently least-loaded machine,
ties broken arbitrarily) has makespan at most `(4/3 - 1/(3m)) · OPT`.

Jobs are `Fin n` (job `i` is the paper's job `i + 1`), machines are `Fin m`, `p` are the
processing times. The load of machine `j` under an assignment `τ` is
`∑ k ∈ univ.filter (τ · = j), p k`; the makespan is the maximum load (`Finset.sup'` over the
machines) and `OPT` is the minimum makespan over all assignments `τ : Fin n → Fin m`
(`Finset.inf'`). Machine `⟨0, hm⟩` witnesses that both index sets are nonempty. -/
theorem lpt_makespan_le (m n : ℕ) (hm : 0 < m) (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsorted : Antitone p) (σ : Fin n → Fin m)
    (hLPT : ∀ i : Fin n, ∀ j : Fin m,
      ∑ k ∈ Finset.univ.filter (fun k => k < i ∧ σ k = σ i), p k ≤
        ∑ k ∈ Finset.univ.filter (fun k => k < i ∧ σ k = j), p k) :
    Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
        (fun j : Fin m => ∑ k ∈ Finset.univ.filter (fun k => σ k = j), p k) ≤
      (4 / 3 - 1 / (3 * (m : ℝ))) *
        Finset.univ.inf' ⟨fun _ => ⟨0, hm⟩, Finset.mem_univ _⟩
          (fun τ : Fin n → Fin m => Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
            (fun j : Fin m => ∑ k ∈ Finset.univ.filter (fun k => τ k = j), p k)) := by
  sorry

end Graham1969
