-- Prove2me | Theorems.Thm_GMRDiversity_theorem_3
-- name    : GMRDiversity.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:42:50.139003+00:00
-- url     : https://prove2.me/theorems/feaa0ebf-fc29-4bdb-9e9e-33ef289a2be7
-- title:
--   Theorem 3 (Diversity is necessary) — parity learning with a live pool of size $w$ needs $\Theta(w+2^{n-w})$ queries
-- statement:
--   Consider parity learning as a generation–recombination problem: a hidden $x\in\{0,1\}^n$ is drawn uniformly; generation returns a uniformly random equation $(a,a\cdot x)$, recombination XORs two equations, and a policy succeeds when it queries the equation $(x,x\cdot x)$. A policy has live pool size $w$ if its entire persistent state is an ordered list of at most $w$ earlier candidates, and every operator argument comes from that list.
--
--   There are constants $c,C>0$ such that for every $n\ge2$ and $1\le w\le n$:
--
--   1. there is a policy $\pi$ with live pool of size $w$ and a horizon $T\le C(w+2^{n-w})$ with $V^\pi_T\ge\frac23$;
--   2. for every policy $\pi$ with live pool size at most $w$ and every $T$, if $V^\pi_T\ge\frac23$ then
--   $$
--   T\ge c\,\big(w+2^{n-w}\big).
--   $$
--
--   So the query complexity of reaching success probability $2/3$ is $\Theta(w+2^{n-w})$: a pool of $w$ candidates saves a factor $2^w$ over pure generation, and nothing beyond that.
--
--   **Formalization Note** $c$ and $C$ are chosen before $n$ and $w$. Part 1 produces a policy that keeps only queried candidates; part 2 covers every policy whose pool entries lie in the span of its previous pool and the new candidate.
--
--   Differences from the source:
--   - generalization: a policy with live pool of size w → a LivePoolPolicy n w that also satisfies RetainsQueried (next pool = old pool plus the new candidate, with deletions and reordering); reason: such a policy is a live-pool policy under every reading of the page, so the existence statement specializes to the page's
--   - generalization: every policy with live pool size at most w → every LivePoolPolicy n w, whose next pool may hold any element of the F₂-span of the previous pool and the new candidate; reason: this class contains the page's policies under every reading of 'previously queried candidates', so the bound for it implies the page's
--   - encoding: live pool size w up to time T → pool length ≤ w at every round; reason: V^π_T depends only on rounds ≤ T; a policy obeying the bound up to T can be changed after T (keep the empty list) without changing V^π_T
--   - encoding: V^π_T = E[max_{t∈[T]} U_x(z_t)] with x uniform → 2^{-n} Σ_x P(some z_t, t ≤ T, has first coordinate x), with V^π_0 = 0; reason: U_x ∈ {0,1}; the empty maximum is 0
--   - encoding: the general GMR framework of Definition 1 with costs c(Gen_x) = c(XOR) = 1 → only the parity instance: candidates V n × ZMod 2, Gen_x as genLaw, XOR as +, U_x as hit; reason: T counts queries, so costs play no role; the page's statements concern 𝔊^par_x only
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), Theorem 3, p.8

import Mathlib
import Definitions.Def_GMRDiversity_value

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Theorem 3 (Diversity is necessary)** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms
with Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, Theorem 3,
p.8): there are `c, C > 0` such that for every `n ≥ 2` and `1 ≤ w ≤ n`:
(i) there is a policy `π` with live pool of size `w` and `T ≤ C(w + 2^{n−w})` with
`V^π_T(𝔊^par_x) ≥ 2/3`;
(ii) for every policy `π` with live pool size at most `w`, if `V^π_T(𝔊^par_x) ≥ 2/3`, then
`T ≥ c(w + 2^{n−w})`.

**Formalization Note.** `c` and `C` are chosen before `n` and `w`. Part (i) produces a policy whose
pools consist of queried candidates only (`RetainsQueried`, the strictest reading of "live pool");
part (ii) covers every `LivePoolPolicy n w`, whose pools may hold any element of the span of the old
pool and the new candidate (the broadest reading). Both readings specialize to the page. -/
theorem theorem_3 : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n w : ℕ, 2 ≤ n → 1 ≤ w → w ≤ n →
    (∃ π : LivePoolPolicy n w, π.RetainsQueried ∧
      ∃ T : ℕ, (T : ℝ) ≤ C * ((w : ℝ) + 2 ^ (n - w)) ∧ 2 / 3 ≤ value π T) ∧
    (∀ (π : LivePoolPolicy n w) (T : ℕ), 2 / 3 ≤ value π T →
      c * ((w : ℝ) + 2 ^ (n - w)) ≤ T) := by sorry

end GMRDiversity
