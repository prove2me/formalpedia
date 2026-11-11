-- Prove2me | Theorems.Thm_MinKCutII_Main_theorem_1
-- name    : MinKCutII.Main.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:41:11.609772+00:00
-- url     : https://prove2.me/theorems/4052ee7b-44f6-4325-bc75-4b0a38e8f666
-- title:
--   Theorem 1 — minimum k-cut in O(m) + k^{O(k²)} n^{k−1} log² n time w.h.p., or deterministically in O(m) + k^{O(k²)} n^{k−1} log^{O(1)} n
-- statement:
--   Inputs are a number $k\ge3$ and an undirected multigraph on $n\ge1$ vertices given by $m$ edge records, each with two endpoints and a positive integer capacity, with total capacity $c(E)\le n^d$. A correct answer is a minimum $k$-cut (a partition into exactly $k$ nonempty parts of value $\lambda_k$) when $n\ge k$, and the flag "infeasible" ($\lambda_k=+\infty$) when $n<k$. Programs run on a unit-cost word RAM with uniformly random words.
--
--   **(R)** For every $d\ge1$ and every $c>0$ there are a constant $C$ and one randomized program such that, for every $k\ge3$ and every such graph, every run halts within
--   $$C\,(m+1)+k^{Ck^2}\,n^{k-1}\,(1+\log_2n)^2$$
--   steps, and except on a set of random tapes of measure at most $n^{-c}$ the answer is correct.
--
--   **(D)** For every $d\ge1$ there are a constant $C$ and one deterministic program that, for every $k\ge3$ and every such graph, halts within $C(m+1)+k^{Ck^2}n^{k-1}(1+\log_2n)^C$ steps with a correct answer.
--
--   This is the paper's headline result: the dense randomized exponent drops from $k$ to $k-1$, and the deterministic exponent matches it.
--
--   Differences from the source:
--
--   - reading: an algorithm running in a given time (no machine model named) → a program of the published randomized word RAM DynConnWC.Program, words of C·⌈log₂(input magnitude + time bound)⌉ bits, input read once in order, output written as words; reason: the paper names no model; this is a standard unit-cost word RAM with Θ(log n)-bit words for fixed k
--   - encoding: a graph with vertex set [n] and its output partition → edge records (u_i, v_i, c_i) on Fin n read as words; a k-cut output as the words 0, f(0), …, f(n−1), the flag [1] for "infeasible"/"certificate"; reason: a fixed input/output layout; vertex indices shifted by one
--   - reading: for every fixed k (constant hidden in k^{O(k²)}) → one program and one constant C for all k, with k part of the input; k^{O(k²)} = k^(C·k²); reason: the stronger reading; k^{O(k²)} is meaningful only with a constant independent of k
--   - reading: with probability 1 − n^{−Ω(1)} → for every c > 0 there are a constant and a program whose failure set of random tapes has measure at most n^(−c); reason: p. 5: the exponent can be increased by changing constants; the measure of the failure set avoids measurability side conditions
--   - reading: runs in T time (randomized) → every run, on every random tape, halts within T steps; reason: the strong worst-case reading; no expected time
--   - encoding: positive polynomially bounded integral capacities → positive integer capacities with c(E) ≤ n^d, for every d ≥ 1 with constants depending on d; reason: the polynomial bound n^{O(1)} with its exponent fixed before the constants
--   - generalization: a weighted multigraph (self-loops are discarded) → input records may be loops; reason: loops cross no cut, so a loopless input is a special case
--   - encoding: an n-vertex graph → 1 ≤ n; reason: graphs are nonempty (λ_1 := 0 is stated for nonempty graphs); log n and n^{−c} are defined
--   - encoding: λ_k = +∞ when n < k → the program outputs the flag [1] when n < k; reason: a minimum k-cut does not exist then; the flag is the paper's +∞ answer
--   - encoding: log n → 1 + log₂ n; reason: nonzero at n = 1; differs from log n by a constant factor for n ≥ 2
--   - reading: After O(m)-time aggregation of parallel edges, … in T time → one program whose total time is at most C·(m + 1) + T, aggregation included; reason: the aggregation is part of the algorithm; its cost is the additive O(m) term
--   - encoding: O(m) + k^{O(k²)} n^{k−1} log² n and O(m) + k^{O(k²)} n^{k−1} log^{O(1)} n → C·(m + 1) + k^(C·k²)·n^(k−1)·(1 + log₂ n)² and C·(m + 1) + k^(C·k²)·n^(k−1)·(1 + log₂ n)^C; reason: every O(·), Õ(·), k^{O(k²)} and log^{O(1)} is an explicit existentially quantified universal constant
--   - reading: Theorem 1 (Informal) → the two clauses as one conjunction, with the formal readings of Theorems 47, 53, 65; reason: the paper labels Theorem 1 informal; its formal counterparts fix the meaning
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 3, Theorem 1

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_KCut
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MinKCutII_Main_Encoding

set_option autoImplicit false

open CombOpt.MinCut DynConnWC MeasureTheory

namespace MinKCutII.Main

/-- **Theorem 1** (p. 3), both clauses. Inputs: undirected multigraphs on `Fin n` (`n ≥ 1`) given
by `m` edge records with positive integer capacities and total capacity `c(E) ≤ n^d`, and a
parameter `k ≥ 3`.

(R) For every `d ≥ 1` and `c > 0` there are a constant `C` and one randomized program `P` such that,
for every `k ≥ 3` and every such graph, every run halts within
`C (m + 1) + k^(C k²) n^(k−1) (1 + log₂ n)²` steps, and outside a set of random tapes of measure at
most `n^(−c)` the output is a minimum k-cut (the flag "infeasible" when `n < k`).

(D) For every `d ≥ 1` there are a constant `C` and one deterministic program that halts within
`C (m + 1) + k^(C k²) n^(k−1) (1 + log₂ n)^C` steps and always outputs a minimum k-cut (or the
flag when `n < k`). -/
theorem theorem_1 :
    (∀ d : ℕ, 1 ≤ d → ∀ c : ℝ, 0 < c → ∃ C : ℕ, 1 ≤ C ∧ ∃ P : Program,
      ∀ (k n m : ℕ) (ed : EdgeRecs n m), 3 ≤ k → 1 ≤ n → (∀ i, 0 < (ed i).2.2) →
        capSum ed ≤ n ^ d →
        let T : ℝ := (C : ℝ) * ((m : ℝ) + 1) +
          (k : ℝ) ^ (C * k ^ 2) * (n : ℝ) ^ (k - 1) * (1 + Real.logb 2 n) ^ 2
        let inp := kGraphInput k ed
        let W := wordSize C inp T
        (∀ ω : ℕ → Fin (2 ^ W), HaltsWithin W P inp ω T) ∧
          tapeLaw W {ω | ¬ IsMinKCutOutput (toGraph ed) k (finalOutput W P inp ω)} ≤
            ENNReal.ofReal ((n : ℝ) ^ (-c))) ∧
    (∀ d : ℕ, 1 ≤ d → ∃ C : ℕ, 1 ≤ C ∧ ∃ P : Program, IsDeterministic P ∧
      ∀ (k n m : ℕ) (ed : EdgeRecs n m), 3 ≤ k → 1 ≤ n → (∀ i, 0 < (ed i).2.2) →
        capSum ed ≤ n ^ d →
        let T : ℝ := (C : ℝ) * ((m : ℝ) + 1) +
          (k : ℝ) ^ (C * k ^ 2) * (n : ℝ) ^ (k - 1) * (1 + Real.logb 2 n) ^ C
        let inp := kGraphInput k ed
        let W := wordSize C inp T
        ∀ ω : ℕ → Fin (2 ^ W), HaltsWithin W P inp ω T ∧
          IsMinKCutOutput (toGraph ed) k (finalOutput W P inp ω)) := by sorry

end MinKCutII.Main
