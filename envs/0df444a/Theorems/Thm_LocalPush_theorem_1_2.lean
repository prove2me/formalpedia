-- Prove2me | Theorems.Thm_LocalPush_theorem_1_2
-- name    : LocalPush.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:22.460528+00:00
-- url     : https://prove2.me/theorems/05800a44-16d1-4dbf-879a-18488a167e04
-- title:
--   Theorem 1.2 — ACL $\varepsilon$-approximate PageRank in $\tilde O(\min\{1/(\sqrt\alpha\,\varepsilon),1/\varepsilon^2\})$ time, $O(1/\varepsilon)$ queries (corrected: logs clamped at 1)
-- statement:
--   There are a program $P$ of the machine `LocalPush.Machine` and a constant $C>0$ such that the following holds for every finite simple undirected graph without isolated nodes, given by adjacency lists in any order, every seed node $s$, every $\alpha\in(0,1)$, every $\varepsilon>0$ and every $\delta\in(0,1)$. On a measurable set of coin tapes of probability at least $1-\delta$, the run of $P$ on input $(s,\alpha,\varepsilon,\delta)$ halts, and:
--
--   1. its output $\tilde p$ is an ACL $\varepsilon$-approximate PageRank vector for the seed $s$ with support volume $\mathrm{vol}(\mathrm{supp}(\tilde p))\le2/\varepsilon$;
--   2. it makes at most $C/\varepsilon$ degree and neighbor queries;
--   3. its running time is at most
--   $$C\Big(1+\min\Big\{\frac{\mathrm L(1/(\alpha\varepsilon))}{\sqrt\alpha\,\varepsilon},\frac1{\varepsilon^2}\Big\}\,\mathrm L\Big(\frac1{\alpha\varepsilon\delta}\Big)\,\mathrm L\Big(\mathrm L\Big(\frac1\varepsilon\Big)\Big)^{13}\Big),\qquad \mathrm L(x)=\max\{1,\log x\}.$$
--
--   The original local push of Andersen, Chung and Lang takes $O(1/(\alpha\varepsilon))$ time; this replaces $1/\alpha$ by $1/\sqrt\alpha$ up to logarithmic factors while keeping the $O(1/\varepsilon)$ query complexity and support volume.
--
--   **Formalization Note** The program receives only $s$, $\alpha$, $\varepsilon$, $\delta$ and reads the graph only through the oracle instructions. The constant $C$ is chosen before the graph and all parameters, so it does not depend on $\alpha$.
--
--   Differences from the source:
--   - correction: O(min{log(1/(αε))/(√α ε), 1/ε²} log(1/(αεδ)) (log log(1/ε))^13) → C·(1 + min{L(1/(αε))/(√α ε), 1/ε²}·L(1/(αεδ))·L(L(1/ε))^13) with L(x) = max{1, log x}; reason: the printed bound is false: at ε = 1/e it equals 0 (log log e = 0) for every constant, and it is negative for ε ∈ (1/e, 1), while every run needs at least one step; for ε ≤ e^{−e} every printed logarithm is ≥ 1 and the corrected bound is at most twice the printed one
--   - reading: "there exists an algorithm" with query complexity O(1/ε) and time complexity O(·) in "the standard adjacency-list model" (p.4) → one admissible program of LocalPush.Machine and one constant C > 0, chosen before the graph, s, α, ε, δ; work and queries counted by the machine; reason: the paper names only the query model; a machine with no free computation gives the strongest reading, and α is not a constant (p.4)
--   - reading: "satisfies the following properties with probability at least 1 − δ" → a measurable set of fair-coin tapes of probability ≥ 1 − δ on which the run halts and all three properties hold; reason: all three bullets sit under the one probability as printed; the randomness of the algorithm is a fair-coin tape
--   - encoding: a graph G = (V, E) accessed in the adjacency-list model; a returned vector → adjacency lists nbrs : Fin n → List (Fin n) satisfying IsAdjList, in any order; the program gets only s, α, ε, δ; the output p̃(v) is real memory at −1 − v; reason: a fixed representation of the same instances; the program is not given n or m, which would only help it
--   - reading: O(·) = Õ(min{1/(√α ε), 1/ε²}) → the explicit O(·) bound only; reason: the trailing Õ(·) restates the explicit bound and follows from it
--   - encoding: pr_α(s) defined as the unique solution of (1) → pr G α σ := α(I − (1 − α)AD⁻¹)⁻¹σ, with D⁻¹ the diagonal of reciprocal degrees; reason: for α ∈ (0, 1) and no isolated nodes the matrix is invertible and this is the unique solution (milestone LocalPush.eq_1_unique); D⁻¹ is the diagonal of reciprocal degrees when degrees are positive
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §1.2, Theorem 1.2, p.5 (PDF p.5)

import Mathlib
import Definitions.Def_LocalPush_PageRank
import Definitions.Def_LocalPush_Layout

open Finset Matrix

namespace LocalPush

/-- **Theorem 1.2 (ActiveSetPush) (corrected: logarithms clamped at 1).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §1.2, Theorem 1.2, p.5 (PDF p.5).

"Given a seed node s ∈ V, α ∈ (0, 1), ε > 0, and δ ∈ (0, 1), there exists an algorithm that satisfies the
following properties with probability at least 1 − δ: • it returns an ACL ε-approximate PageRank vector with
support volume at most 2/ε; • its query complexity is O(1/ε); • its time complexity is
O(min{log(1/(αε))/(√α ε), 1/ε²} log(1/(αεδ)) (log log(1/ε))^13) = Õ(min{1/(√α ε), 1/ε²})."

There are one admissible program `P` of the machine `LocalPush.Machine` and a constant `C > 0` such that for
every graph given by adjacency lists in any order (`IsAdjList`: simple, no isolated nodes), every seed `s` and
all `α ∈ (0, 1)`, `ε > 0`, `δ ∈ (0, 1)`, there is a measurable set `E` of coin tapes of probability at least
`1 − δ` on which the run of `P` on input `(s, α, ε, δ)` halts after some `t` steps with
1. `work ≤ C·(1 + min{L(1/(αε))/(√α ε), 1/ε²}·L(1/(αεδ))·L(L(1/ε))^13)`, where `L(x) = max{1, log x}`;
2. at most `C/ε` oracle queries;
3. an output vector `p̃` (real memory at `−1 − v`) that is an ACL `ε`-approximate PageRank vector for `e_s`
   with `vol(supp(p̃)) ≤ 2/ε`.

**Formalization Note.**
* The machine is a reading: the paper names only the adjacency-list query model (p.4). The program receives
  only `s`, `α`, `ε`, `δ`, never `n`, `m` or the lists; it reads the graph only through the `deg` and `nbr`
  oracle instructions, each counted as a query.
* The three clauses hold together on one measurable event of probability at least `1 − δ`, as printed; nothing
  is required off that event.
* The printed bound is `0` at `ε = 1/e` (`log log e = 0`) and negative for `ε ∈ (1/e, 1)`, where every run needs
  at least one step. Each logarithm is clamped at `1` and `1` is added; for `ε ≤ e^{−e}` this is the printed
  bound up to a factor `2` in the constant.
* `P` and `C` are chosen before the graph and the parameters: the constant is uniform in `α` (p.4: "we do not
  regard α as a constant").
* `pr` is defined through a matrix inverse; for `α ∈ (0, 1)` and no isolated nodes it is the unique solution of
  (1) (milestone `LocalPush.eq_1_unique`). -/
theorem theorem_1_2 :
    ∃ P : Program, Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (nbrs : Fin n → List (Fin n)), IsAdjList nbrs →
      ∀ (s : Fin n) (α ε δ : ℝ), 0 < α → α < 1 → 0 < ε → 0 < δ → δ < 1 →
        ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ coinTape E ∧
          ∀ ω ∈ E, ∃ t : ℕ,
            (run P nbrs (pushInput s α ε δ) ω t).halted = true ∧
            ((run P nbrs (pushInput s α ε δ) ω t).work : ℝ) ≤
              C * (1 + min (clog (1 / (α * ε)) / (Real.sqrt α * ε)) (1 / ε ^ 2) *
                clog (1 / (α * ε * δ)) * clog (clog (1 / ε)) ^ 13) ∧
            ((run P nbrs (pushInput s α ε δ) ω t).queries : ℝ) ≤ C / ε ∧
            IsACL (toGraph nbrs) α (e s) ε (outVec n (run P nbrs (pushInput s α ε δ) ω t)) ∧
            vol (toGraph nbrs) (supp (outVec n (run P nbrs (pushInput s α ε δ) ω t))) ≤ 2 / ε := by sorry

end LocalPush
