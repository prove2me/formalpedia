-- Prove2me | Theorems.Thm_MinKCutII_Main_theorem_65
-- name    : MinKCutII.Main.theorem_65
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:40:59.970295+00:00
-- url     : https://prove2.me/theorems/3438406b-871c-480f-bb71-72fbec5b166b
-- title:
--   Theorem 65 — deterministic minimum k-cut for k ≥ 4 in k^{O(k²)}(n^{k−4}m + n^{k−1}) log^{O(1)} n time
-- statement:
--   For every $d\ge1$ there are a constant $C$ and one deterministic word-RAM program such that, for every $k\ge4$ and every multigraph on $n\ge1$ vertices given by $m$ edge records with positive integer capacities and $c(E)\le n^d$, it halts within
--   $$k^{Ck^2}\,\big(n^{k-4}m+n^{k-1}\big)\,(1+\log_2n)^C$$
--   steps (in particular within $k^{Ck^2}n^{k-3}(m+n^2)(1+\log_2n)^C$ steps) and outputs a minimum $k$-cut (the flag "infeasible" when $n<k$).
--
--   With Theorem 53 for $k=3$ it gives the deterministic clause of Theorem 1. Findings I1 and I2 concern its proof, not its statement.
--
--   Differences from the source:
--
--   - reading: an algorithm running in a given time (no machine model named) → a program of the published randomized word RAM DynConnWC.Program, words of C·⌈log₂(input magnitude + time bound)⌉ bits, input read once in order, output written as words; reason: the paper names no model; this is a standard unit-cost word RAM with Θ(log n)-bit words for fixed k
--   - encoding: a graph with vertex set [n] and its output partition → edge records (u_i, v_i, c_i) on Fin n read as words; a k-cut output as the words 0, f(0), …, f(n−1), the flag [1] for "infeasible"/"certificate"; reason: a fixed input/output layout; vertex indices shifted by one
--   - encoding: deterministic algorithm → a program with no rand instruction (the statement is quantified over all tapes); reason: without rand the run does not depend on the tape
--   - reading: for every fixed k (constant hidden in k^{O(k²)}) → one program and one constant C for all k, with k part of the input; k^{O(k²)} = k^(C·k²); reason: the stronger reading; k^{O(k²)} is meaningful only with a constant independent of k
--   - encoding: positive polynomially bounded integral capacities → positive integer capacities with c(E) ≤ n^d, for every d ≥ 1 with constants depending on d; reason: the polynomial bound n^{O(1)} with its exponent fixed before the constants
--   - generalization: a weighted multigraph (self-loops are discarded) → input records may be loops; reason: loops cross no cut, so a loopless input is a special case
--   - encoding: an n-vertex graph → 1 ≤ n; reason: graphs are nonempty (λ_1 := 0 is stated for nonempty graphs); log n and n^{−c} are defined
--   - encoding: λ_k = +∞ when n < k → the program outputs the flag [1] when n < k; reason: a minimum k-cut does not exist then; the flag is the paper's +∞ answer
--   - encoding: log n → 1 + log₂ n; reason: nonzero at n = 1; differs from log n by a constant factor for n ≥ 2
--   - encoding: k^{O(k²)}(n^{k−4}m + n^{k−1}) log^{O(1)} n; in particular k^{O(k²)} n^{k−3}(m + n²) log^{O(1)} n → k^(C·k²)·(n^(k−4)·m + n^(k−1))·(1 + log₂ n)^C and k^(C·k²)·n^(k−3)·(m + n²)·(1 + log₂ n)^C, both for the same run; reason: every O(·), Õ(·), k^{O(k²)} and log^{O(1)} is an explicit existentially quantified universal constant
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 45, Theorem 65

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_KCut
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MinKCutII_Main_Encoding

set_option autoImplicit false

open CombOpt.MinCut DynConnWC MeasureTheory

namespace MinKCutII.Main

/-- **Theorem 65** (p. 45). For every `d ≥ 1` there are a constant `C` and one deterministic program
such that, for every `k ≥ 4` and every multigraph on `Fin n` (`n ≥ 1`) with positive integer
capacities and `c(E) ≤ n^d`, it halts within `k^(C k²) (n^(k−4) m + n^(k−1)) (1 + log₂ n)^C` steps,
and within `k^(C k²) n^(k−3) (m + n²) (1 + log₂ n)^C` steps (the "in particular" form), and outputs
a minimum k-cut (the flag "infeasible" when `n < k`). -/
theorem theorem_65 :
    ∀ d : ℕ, 1 ≤ d → ∃ C : ℕ, 1 ≤ C ∧ ∃ P : Program, IsDeterministic P ∧
      ∀ (k n m : ℕ) (ed : EdgeRecs n m), 4 ≤ k → 1 ≤ n → (∀ i, 0 < (ed i).2.2) →
        capSum ed ≤ n ^ d →
        let T : ℝ := (k : ℝ) ^ (C * k ^ 2) * ((n : ℝ) ^ (k - 4) * m + (n : ℝ) ^ (k - 1)) *
          (1 + Real.logb 2 n) ^ C
        let T' : ℝ := (k : ℝ) ^ (C * k ^ 2) * (n : ℝ) ^ (k - 3) * ((m : ℝ) + (n : ℝ) ^ 2) *
          (1 + Real.logb 2 n) ^ C
        let inp := kGraphInput k ed
        let W := wordSize C inp T
        ∀ ω : ℕ → Fin (2 ^ W), HaltsWithin W P inp ω T ∧ HaltsWithin W P inp ω T' ∧
          IsMinKCutOutput (toGraph ed) k (finalOutput W P inp ω) := by sorry

end MinKCutII.Main
