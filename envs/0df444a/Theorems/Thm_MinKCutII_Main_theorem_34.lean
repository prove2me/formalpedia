-- Prove2me | Theorems.Thm_MinKCutII_Main_theorem_34
-- name    : MinKCutII.Main.theorem_34
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:40:20.325104+00:00
-- url     : https://prove2.me/theorems/5a8a8955-acba-4deb-b262-09a5bc4ec4da
-- title:
--   Theorem 34 — randomized minimum 3-cut in O((m + n²) log² n) time and O(m + n²) space w.h.p.
-- statement:
--   Inputs are connected multigraphs on $n\ge3$ vertices given by $m$ edge records with positive integer capacities and total capacity $c(E)\le n^d$. For every $d\ge1$ and every $c>0$ there are a constant $C$ and one randomized word-RAM program such that on every such input every run halts within
--   $$C\,(m+n^2)\,(1+\log_2n)^2$$
--   steps and touches at most $C(m+n^2)$ memory cells, and, except on a set of random tapes of measure at most $n^{-c}$, outputs a minimum 3-cut.
--
--   This is the base case of the reduction (Theorem 47) and the new 3-cut bound of the paper.
--
--   Differences from the source:
--
--   - reading: an algorithm running in a given time (no machine model named) → a program of the published randomized word RAM DynConnWC.Program, words of C·⌈log₂(input magnitude + time bound)⌉ bits, input read once in order, output written as words; reason: the paper names no model; this is a standard unit-cost word RAM with Θ(log n)-bit words for fixed k
--   - encoding: a graph with vertex set [n] and its output partition → edge records (u_i, v_i, c_i) on Fin n read as words; a k-cut output as the words 0, f(0), …, f(n−1), the flag [1] for "infeasible"/"certificate"; reason: a fixed input/output layout; vertex indices shifted by one
--   - reading: with probability 1 − n^{−Ω(1)} → for every c > 0 there are a constant and a program whose failure set of random tapes has measure at most n^(−c); reason: p. 5: the exponent can be increased by changing constants; the measure of the failure set avoids measurability side conditions
--   - reading: runs in T time (randomized) → every run, on every random tape, halts within T steps; reason: the strong worst-case reading; no expected time
--   - encoding: positive polynomially bounded integral capacities → positive integer capacities with c(E) ≤ n^d, for every d ≥ 1 with constants depending on d; reason: the polynomial bound n^{O(1)} with its exponent fixed before the constants
--   - generalization: a weighted multigraph (self-loops are discarded) → input records may be loops; reason: loops cross no cut, so a loopless input is a special case
--   - encoding: O((m + n²) log² n) time, O(m + n²) working space → C·(m + n²)·(1 + log₂ n)² steps and at most C·(m + n²) memory cells touched; reason: every O(·), Õ(·), k^{O(k²)} and log^{O(1)} is an explicit existentially quantified universal constant
--   - encoding: log n → 1 + log₂ n; reason: nonzero at n = 1; differs from log n by a constant factor for n ≥ 2
--   - reading: working space → the number of distinct memory cells touched by the run; reason: the input is read once and occupies memory only when stored
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 25, Theorem 34

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_KCut
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MinKCutII_Main_Encoding

set_option autoImplicit false

open CombOpt.MinCut DynConnWC MeasureTheory

namespace MinKCutII.Main

/-- **Theorem 34** (p. 25). For every `d ≥ 1` and `c > 0` there are a constant `C` and one randomized
program `P` such that, on every connected multigraph on `Fin n` with `n ≥ 3`, positive integer
capacities and `c(E) ≤ n^d`, every run halts within `C (m + n²) (1 + log₂ n)²` steps and touches at
most `C (m + n²)` memory cells, and outside a set of random tapes of measure at most `n^(−c)` the
output is a minimum 3-cut. -/
theorem theorem_34 :
    ∀ d : ℕ, 1 ≤ d → ∀ c : ℝ, 0 < c → ∃ C : ℕ, 1 ≤ C ∧ ∃ P : Program,
      ∀ (n m : ℕ) (ed : EdgeRecs n m), 3 ≤ n → (∀ i, 0 < (ed i).2.2) → capSum ed ≤ n ^ d →
        IsConnected (toGraph ed) →
        let T : ℝ := (C : ℝ) * ((m : ℝ) + (n : ℝ) ^ 2) * (1 + Real.logb 2 n) ^ 2
        let inp := graphInput ed
        let W := wordSize C inp T
        (∀ ω : ℕ → Fin (2 ^ W), HaltsWithin W P inp ω T ∧
            SpaceWithin W P inp ω ((C : ℝ) * ((m : ℝ) + (n : ℝ) ^ 2))) ∧
          tapeLaw W {ω | ¬ IsMinKCutOutput (toGraph ed) 3 (finalOutput W P inp ω)} ≤
            ENNReal.ofReal ((n : ℝ) ^ (-c)) := by sorry

end MinKCutII.Main
