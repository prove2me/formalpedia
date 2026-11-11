-- Prove2me | Theorems.Thm_MinKCutII_Main_theorem_58
-- name    : MinKCutII.Main.theorem_58
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:40:50.37066+00:00
-- url     : https://prove2.me/theorems/6dd61cba-0eb6-4303-a541-1a216b5fd6cf
-- title:
--   Theorem 58 — deterministic minimum 4-cut in O(m) + Õ(n³) time
-- statement:
--   For every $d\ge1$ there are a constant $C$ and one deterministic word-RAM program that, on every multigraph on $n\ge1$ vertices given by $m$ edge records with positive integer capacities and $c(E)\le n^d$, halts within
--   $$C\,(m+1)+C\,n^3\,(1+\log_2n)^C$$
--   steps and outputs a minimum 4-cut (the flag "infeasible" when $n<4$).
--
--   It is the $k=4$ base case of the derandomized reduction (Theorem 65).
--
--   Differences from the source:
--
--   - reading: an algorithm running in a given time (no machine model named) → a program of the published randomized word RAM DynConnWC.Program, words of C·⌈log₂(input magnitude + time bound)⌉ bits, input read once in order, output written as words; reason: the paper names no model; this is a standard unit-cost word RAM with Θ(log n)-bit words for fixed k
--   - encoding: a graph with vertex set [n] and its output partition → edge records (u_i, v_i, c_i) on Fin n read as words; a k-cut output as the words 0, f(0), …, f(n−1), the flag [1] for "infeasible"/"certificate"; reason: a fixed input/output layout; vertex indices shifted by one
--   - encoding: deterministic algorithm → a program with no rand instruction (the statement is quantified over all tapes); reason: without rand the run does not depend on the tape
--   - encoding: positive polynomially bounded integral capacities → positive integer capacities with c(E) ≤ n^d, for every d ≥ 1 with constants depending on d; reason: the polynomial bound n^{O(1)} with its exponent fixed before the constants
--   - generalization: a weighted multigraph (self-loops are discarded) → input records may be loops; reason: loops cross no cut, so a loopless input is a special case
--   - encoding: an n-vertex graph → 1 ≤ n; reason: graphs are nonempty (λ_1 := 0 is stated for nonempty graphs); log n and n^{−c} are defined
--   - encoding: log n → 1 + log₂ n; reason: nonzero at n = 1; differs from log n by a constant factor for n ≥ 2
--   - encoding: O(m) + Õ(n³) → C·(m + 1) + C·n³·(1 + log₂ n)^C; reason: every O(·), Õ(·), k^{O(k²)} and log^{O(1)} is an explicit existentially quantified universal constant
--   - encoding: a minimum 4-cut (n < 4: none exists) → the flag [1] when n < 4; reason: λ₄ = +∞ then
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 42, Theorem 58

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_KCut
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MinKCutII_Main_Encoding

set_option autoImplicit false

open CombOpt.MinCut DynConnWC MeasureTheory

namespace MinKCutII.Main

/-- **Theorem 58** (p. 42). For every `d ≥ 1` there are a constant `C` and one deterministic program
that, on every multigraph on `Fin n` (`n ≥ 1`) with positive integer capacities and `c(E) ≤ n^d`,
halts within `C (m + 1) + C n³ (1 + log₂ n)^C` steps and outputs a minimum 4-cut (the flag
"infeasible" when `n < 4`). -/
theorem theorem_58 :
    ∀ d : ℕ, 1 ≤ d → ∃ C : ℕ, 1 ≤ C ∧ ∃ P : Program, IsDeterministic P ∧
      ∀ (n m : ℕ) (ed : EdgeRecs n m), 1 ≤ n → (∀ i, 0 < (ed i).2.2) → capSum ed ≤ n ^ d →
        let T : ℝ := (C : ℝ) * ((m : ℝ) + 1) + (C : ℝ) * (n : ℝ) ^ 3 * (1 + Real.logb 2 n) ^ C
        let inp := graphInput ed
        let W := wordSize C inp T
        ∀ ω : ℕ → Fin (2 ^ W), HaltsWithin W P inp ω T ∧
          IsMinKCutOutput (toGraph ed) 4 (finalOutput W P inp ω) := by sorry

end MinKCutII.Main
