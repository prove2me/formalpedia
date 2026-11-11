-- Prove2me | Theorems.Thm_MinKCutII_Main_corollary_42
-- name    : MinKCutII.Main.corollary_42
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:40:51.607203+00:00
-- url     : https://prove2.me/theorems/41f7c04c-98f4-412a-9416-7a81fadac6c0
-- title:
--   Corollary 42 — more than C_k n distinct light cuts force an explicit k-cut of value at most U
-- statement:
--   With $G,k,U,r$ as in Lemma 41, there are a universal constant $C$, constants $C_k$ as in Lemma 41 ($C_k\le C(kD_k+2^k)$, $C_k\le(Ck\log k)^k$) and one deterministic program which, given a list of $N>C_kn$ distinct rooted cuts with $c_G(S)\le2U/k$ (edge records first, then the incidence vectors), outputs a $k$-cut of value at most $U$ within
--   $$k^{Ck^2}\big(C_kn^3(1+\log_2n)+mn+1\big)\quad\text{and within}\quad k^{Ck^2}\big(n^3(1+\log_2n)+mn+1\big)$$
--   steps.
--
--   This is the overflow rule used by the reduction when too many light cuts are found.
--
--   Differences from the source:
--
--   - reading: an algorithm running in a given time (no machine model named) → a program of the published randomized word RAM DynConnWC.Program, words of C·⌈log₂(input magnitude + time bound)⌉ bits, input read once in order, output written as words; reason: the paper names no model; this is a standard unit-cost word RAM with Θ(log n)-bit words for fixed k
--   - encoding: a connected capacitated multigraph with a cut family → edge records (u_i, v_i, c_i) on Fin n, then the incidence vectors; k-cut output as words 0, f(0), …, f(n−1); flag [1]; reason: a fixed input/output layout
--   - encoding: deterministic algorithm → a program with no rand instruction (the statement is quantified over all tapes); reason: without rand the run does not depend on the tape
--   - encoding: a threshold U > 0 → U = p/q given by two positive integers; reason: an algorithm input is finite; every threshold the paper passes (kB/2) is rational
--   - encoding: a family of distinct cuts, oriented away from a fixed root r → N rooted cuts S_i (nonempty, r ∉ S_i), pairwise distinct, given by incidence vectors after the edge records; r is an input; reason: §4.1: all cuts are oriented away from a fixed root; distinct rooted cuts are distinct bipartitions
--   - generalization: capacities with total c(E) ≤ n^{O(1)} (§2 standing convention) → positive integer capacities of any size; reason: the word size grows with log c(E), so the bounded case is a special case
--   - generalization: a weighted multigraph (self-loops are discarded) → input records may be loops; reason: loops cross no cut, so a loopless input is a special case
--   - reading: There is a constant C_k = O(kD_k + 2^k) … with the bound Sun(k, k+1) ≤ (Ck log k)^k, C_k ≤ (C′k log k)^k → a function C_k with C_k ≤ C·(k·D_k + 2^k) and C_k ≤ (C·k·ln k)^k for all k ≥ 3, the same C_k in the certificate; reason: both clauses are part of the statement; one universal constant serves for both O-constants
--   - reading: OverflowCertificate, applied to the first C_k n + 1 such cuts; the additional time → one deterministic program on the whole list, whose running time is bounded independently of N; reason: the bound does not depend on N, so the program can only use a prefix of the list; the edge records come first
--   - encoding: k^{O(k²)}(C_k n³ log n + mn) and k^{O(k²)}(n³ log n + mn) → k^(C·k²)·(C_k·n³·(1 + log₂ n) + m·n + 1) and k^(C·k²)·(n³·(1 + log₂ n) + m·n + 1); reason: every O(·), Õ(·), k^{O(k²)} and log^{O(1)} is an explicit existentially quantified universal constant
--   - encoding: O(f) → C·(f + 1); reason: a program takes at least one step even when f = 0
--   - encoding: log n → 1 + log₂ n; reason: nonzero at n = 1; differs from log n by a constant factor for n ≥ 2
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 30, Corollary 42

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_KCut
import Definitions.Def_MinKCutII_Main_Cuts
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MinKCutII_Main_Encoding
import Definitions.Def_MinKCutII_Main_Sunflower

set_option autoImplicit false

open CombOpt.MinCut DynConnWC

namespace MinKCutII.Main

/-- **Corollary 42** (p. 30). There are a constant `C`, constants `C_k` as in Lemma 41
(`C_k ≤ C (k D_k + 2^k)`, `C_k ≤ (C k log k)^k`) and one deterministic program which, given a
connected multigraph on `Fin n` with positive integer capacities, `k ≥ 3`, `U = p/q > 0`, a root
`r` and a list of `N > C_k n` distinct rooted cuts with `c_G(S) ≤ 2U/k` (edges first, then the
cuts), outputs a k-cut of value at most `U` within `k^(C k²) (C_k n³ (1 + log₂ n) + m n + 1)` steps,
and within `k^(C k²) (n³ (1 + log₂ n) + m n + 1)` steps. -/
theorem corollary_42 :
    ∃ C : ℕ, 1 ≤ C ∧ ∃ Ck : ℕ → ℕ,
      (∀ k : ℕ, 3 ≤ k → Ck k ≤ C * (k * Dk k + 2 ^ k)) ∧
      (∀ k : ℕ, 3 ≤ k → (Ck k : ℝ) ≤ ((C : ℝ) * k * Real.log k) ^ k) ∧
      ∃ P : Program, IsDeterministic P ∧
      ∀ (n m k p q : ℕ) (r : Fin n) (N : ℕ) (ed : EdgeRecs n m) (S : ℕ → Finset (Fin n)),
        3 ≤ k → 0 < p → 0 < q → (∀ i, 0 < (ed i).2.2) → IsConnected (toGraph ed) →
        (∀ i j, i < N → j < N → S i = S j → i = j) →
        (∀ i, i < N → IsRootedCut r (S i) ∧ IsULight (toGraph ed) k ((p : ℝ) / q) (S i)) →
        Ck k * n < N →
        let T : ℝ := (k : ℝ) ^ (C * k ^ 2) *
          ((Ck k : ℝ) * (n : ℝ) ^ 3 * (1 + Real.logb 2 n) + (m : ℝ) * n + 1)
        let T' : ℝ := (k : ℝ) ^ (C * k ^ 2) *
          ((n : ℝ) ^ 3 * (1 + Real.logb 2 n) + (m : ℝ) * n + 1)
        let inp := familyInput k p q r N ed S
        let W := wordSize C inp T
        ∀ ω : ℕ → Fin (2 ^ W), HaltsWithin W P inp ω T ∧ HaltsWithin W P inp ω T' ∧
          IsKCutAtMostOutput (toGraph ed) k ((p : ℝ) / q) (finalOutput W P inp ω) := by sorry

end MinKCutII.Main
