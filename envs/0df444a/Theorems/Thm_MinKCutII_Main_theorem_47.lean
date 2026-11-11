-- Prove2me | Theorems.Thm_MinKCutII_Main_theorem_47
-- name    : MinKCutII.Main.theorem_47
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:40:54.560849+00:00
-- url     : https://prove2.me/theorems/1492e44c-2d42-4e0f-b0a1-2991c51653d8
-- title:
--   Theorem 47 — randomized minimum k-cut w.h.p. in k^{O(k²)} n^{k−3}(m + n²) log² n time
-- statement:
--   Inputs are a number $k\ge3$ and a multigraph on $n\ge1$ vertices given by $m$ edge records with positive integer capacities and $c(E)\le n^d$. For every $d\ge1$ and $c>0$ there are a constant $C$ and one randomized word-RAM program such that, for every $k\ge3$ and every such graph, every run halts within
--   $$k^{Ck^2}\,n^{k-3}\,(m+n^2)\,(1+\log_2n)^2$$
--   steps, and except on a set of random tapes of measure at most $n^{-c}$ the output is a minimum $k$-cut (the flag "infeasible" when $n<k$).
--
--   It reduces Minimum $k$-Cut to Minimum 3-Cut and gives the randomized clause of Theorem 1.
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
--   - encoding: k^{O(k²)} n^{k−3}(m + n²) log² n → k^(C·k²)·n^(k−3)·(m + n²)·(1 + log₂ n)²; reason: every O(·), Õ(·), k^{O(k²)} and log^{O(1)} is an explicit existentially quantified universal constant
--   - reading: Algorithm 5 returns …; The randomness is confined to the randomized 2- and 3-cut base cases and to sampling from the tree-packing distributions → there is a randomized program with the guarantee; the last sentence is not formalized; reason: it describes Algorithm 5 and has no content for an existence statement
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 35, Theorem 47

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_KCut
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MinKCutII_Main_Encoding

set_option autoImplicit false

open CombOpt.MinCut DynConnWC MeasureTheory

namespace MinKCutII.Main

/-- **Theorem 47** (p. 35). For every `d ≥ 1` and `c > 0` there are a constant `C` and one randomized
program `P` such that, for every `k ≥ 3` and every multigraph on `Fin n` (`n ≥ 1`) with positive
integer capacities and `c(E) ≤ n^d`, every run halts within `k^(C k²) n^(k−3) (m + n²) (1 + log₂ n)²`
steps, and outside a set of random tapes of measure at most `n^(−c)` the output is a minimum
k-cut (the flag "infeasible" when `n < k`). -/
theorem theorem_47 :
    ∀ d : ℕ, 1 ≤ d → ∀ c : ℝ, 0 < c → ∃ C : ℕ, 1 ≤ C ∧ ∃ P : Program,
      ∀ (k n m : ℕ) (ed : EdgeRecs n m), 3 ≤ k → 1 ≤ n → (∀ i, 0 < (ed i).2.2) →
        capSum ed ≤ n ^ d →
        let T : ℝ := (k : ℝ) ^ (C * k ^ 2) * (n : ℝ) ^ (k - 3) * ((m : ℝ) + (n : ℝ) ^ 2) *
          (1 + Real.logb 2 n) ^ 2
        let inp := kGraphInput k ed
        let W := wordSize C inp T
        (∀ ω : ℕ → Fin (2 ^ W), HaltsWithin W P inp ω T) ∧
          tapeLaw W {ω | ¬ IsMinKCutOutput (toGraph ed) k (finalOutput W P inp ω)} ≤
            ENNReal.ofReal ((n : ℝ) ^ (-c)) := by sorry

end MinKCutII.Main
