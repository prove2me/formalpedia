-- Prove2me | Theorems.Thm_MinKCutII_Main_lemma_41
-- name    : MinKCutII.Main.lemma_41
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:40:52.320197+00:00
-- url     : https://prove2.me/theorems/f57be0c8-56c9-4c6f-a950-d9c6dc24b5b3
-- title:
--   Lemma 41 — constructive overflow certificate: a k-cut of value at most U, or |F| ≤ C_k n, in k^{O(k²)}(|F| n² log n + mn) time
-- statement:
--   Let $G$ be a connected multigraph on $n$ vertices with $m$ positive integer capacity records, $k\ge3$, $U>0$, $r$ a root, and $\mathcal F$ a family of $N$ distinct rooted cuts with $c_G(S)\le2U/k$. There are a universal constant $C$, constants $C_k$ with
--   $$C_k\le C\,(kD_k+2^k),\qquad C_k\le(Ck\log k)^k\quad(k\ge3),$$
--   and one deterministic program which, given $\mathcal F$ by incidence vectors, halts within $k^{Ck^2}\big(Nn^2(1+\log_2n)+mn+1\big)$ steps and either outputs a $k$-cut of value at most $U$, or outputs the certificate flag, in which case $N\le C_kn$.
--
--   It turns an overflowing family of light cuts into an explicit $k$-cut, which the reduction needs on overflow.
--
--   Differences from the source:
--
--   - reading: an algorithm running in a given time (no machine model named) → a program of the published randomized word RAM DynConnWC.Program, words of C·⌈log₂(input magnitude + time bound)⌉ bits, input read once in order, output written as words; reason: the paper names no model; this is a standard unit-cost word RAM with Θ(log n)-bit words for fixed k
--   - encoding: a connected capacitated multigraph with a cut family → edge records (u_i, v_i, c_i) on Fin n, then the incidence vectors; k-cut output as words 0, f(0), …, f(n−1); flag [1]; reason: a fixed input/output layout
--   - encoding: deterministic algorithm → a program with no rand instruction (the statement is quantified over all tapes); reason: without rand the run does not depend on the tape
--   - encoding: a threshold U > 0 → U = p/q given by two positive integers; reason: an algorithm input is finite; every threshold the paper passes (kB/2) is rational
--   - encoding: a family of distinct cuts, oriented away from a fixed root r → N rooted cuts S_i (nonempty, r ∉ S_i), pairwise distinct, given by incidence vectors after the edge records; r is an input; reason: §4.1: all cuts are oriented away from a fixed root; distinct rooted cuts are distinct bipartitions
--   - reading: either outputs a k-cut of value at most U, or certifies |·| ≤ B → the output is a k-cut of value at most U, or the flag [1], and whenever the flag is output the bound holds; reason: a certificate is an output after which the bound is guaranteed
--   - generalization: capacities with total c(E) ≤ n^{O(1)} (§2 standing convention) → positive integer capacities of any size; reason: the word size grows with log c(E), so the bounded case is a special case
--   - generalization: a weighted multigraph (self-loops are discarded) → input records may be loops; reason: loops cross no cut, so a loopless input is a special case
--   - reading: There is a constant C_k = O(kD_k + 2^k) … with the bound Sun(k, k+1) ≤ (Ck log k)^k, C_k ≤ (C′k log k)^k → a function C_k with C_k ≤ C·(k·D_k + 2^k) and C_k ≤ (C·k·ln k)^k for all k ≥ 3, the same C_k in the certificate; reason: both clauses are part of the statement; one universal constant serves for both O-constants
--   - reading: Algorithm 4 has the following guarantee → there is a deterministic program with the guarantee; reason: statements about one fixed pseudocode are not posed; existence of a program carries the content
--   - encoding: k^{O(k²)}(|F| n² log n + mn) → k^(C·k²)·(N·n²·(1 + log₂ n) + m·n + 1); reason: every O(·), Õ(·), k^{O(k²)} and log^{O(1)} is an explicit existentially quantified universal constant
--   - encoding: O(f) → C·(f + 1); reason: a program takes at least one step even when f = 0
--   - encoding: log n → 1 + log₂ n; reason: nonzero at n = 1; differs from log n by a constant factor for n ≥ 2
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 29, Lemma 41

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

/-- **Lemma 41** (p. 29). There are a constant `C` and constants `C_k` with `C_k ≤ C (k D_k + 2^k)`
and `C_k ≤ (C k log k)^k` for every `k ≥ 3`, and one deterministic program which, given a
connected multigraph on `Fin n` with positive integer capacities, `k ≥ 3`, `U = p/q > 0`, a root
`r` and a family of `N` distinct rooted cuts with `c_G(S) ≤ 2U/k`, within
`k^(C k²) (N n² (1 + log₂ n) + m n + 1)` steps either outputs a k-cut of value at most `U`, or
outputs the certificate flag, and then `N ≤ C_k n`. -/
theorem lemma_41 :
    ∃ C : ℕ, 1 ≤ C ∧ ∃ Ck : ℕ → ℕ,
      (∀ k : ℕ, 3 ≤ k → Ck k ≤ C * (k * Dk k + 2 ^ k)) ∧
      (∀ k : ℕ, 3 ≤ k → (Ck k : ℝ) ≤ ((C : ℝ) * k * Real.log k) ^ k) ∧
      ∃ P : Program, IsDeterministic P ∧
      ∀ (n m k p q : ℕ) (r : Fin n) (N : ℕ) (ed : EdgeRecs n m) (S : ℕ → Finset (Fin n)),
        3 ≤ k → 0 < p → 0 < q → (∀ i, 0 < (ed i).2.2) → IsConnected (toGraph ed) →
        (∀ i j, i < N → j < N → S i = S j → i = j) →
        (∀ i, i < N → IsRootedCut r (S i) ∧ IsULight (toGraph ed) k ((p : ℝ) / q) (S i)) →
        let T : ℝ := (k : ℝ) ^ (C * k ^ 2) *
          ((N : ℝ) * (n : ℝ) ^ 2 * (1 + Real.logb 2 n) + (m : ℝ) * n + 1)
        let inp := familyInput k p q r N ed S
        let W := wordSize C inp T
        ∀ ω : ℕ → Fin (2 ^ W), HaltsWithin W P inp ω T ∧
          (IsKCutAtMostOutput (toGraph ed) k ((p : ℝ) / q) (finalOutput W P inp ω) ∨
            (finalOutput W P inp ω = flagOut ∧ N ≤ Ck k * n)) := by sorry

end MinKCutII.Main
