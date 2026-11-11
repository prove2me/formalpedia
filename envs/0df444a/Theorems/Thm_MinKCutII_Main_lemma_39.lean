-- Prove2me | Theorems.Thm_MinKCutII_Main_lemma_39
-- name    : MinKCutII.Main.lemma_39
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:40:56.654495+00:00
-- url     : https://prove2.me/theorems/84a66fec-c41a-4cfe-9f17-2e514e6af429
-- title:
--   Lemma 39 — sunflower certificate for medium cuts with shores of size at most k: a k-cut ≤ U or |M| ≤ D_k n
-- statement:
--   With $G,k,U,r$ as in Lemma 36, let $\mathcal M$ be a family of $N$ distinct $U$-medium rooted cuts ($U/(k-1)<c_G(S)\le2U/k$), each with shore size $\min(|S|,n-|S|)\le k$. (i) There are a constant $C$ and one deterministic program which, given $\mathcal M$ by incidence vectors, halts within
--   $$k^{Ck^2}\,(Nn+m+1)\,(1+\log_2n)^C$$
--   steps and either outputs a $k$-cut of value at most $U$, or outputs the certificate flag, in which case $N\le D_kn$ with $D_k=\mathrm{Sun}(k,k+1)(2^k+1)$. (ii) There is $C'>0$ with $D_k\le(C'k\log k)^k$ for every $k\ge3$.
--
--   This handles the medium cuts with small shores in the overflow certificate.
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
--   - encoding: k^{O(k²)} Õ(|M| n + m) → k^(C·k²)·(N·n + m + 1)·(1 + log₂ n)^C; reason: every O(·), Õ(·), k^{O(k²)} and log^{O(1)} is an explicit existentially quantified universal constant
--   - encoding: O(f) → C·(f + 1); reason: a program takes at least one step even when f = 0
--   - encoding: log n → 1 + log₂ n; reason: nonzero at n = 1; differs from log n by a constant factor for n ≥ 2
--   - encoding: Sun(k, k+1), "a sunflower number" → the least sunflower number sunNum k (k+1); reason: the strongest choice of the number; D_k is then as small as possible
--   - reading: In particular, using Sun(k, k+1) ≤ (Ck log k)^k, D_k ≤ (C′k log k)^k → a separate conjunct: some C′ > 0 has D_k ≤ (C′·k·ln k)^k for all k ≥ 3; reason: the clause is part of the statement; the base of log is absorbed by C′
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 27, Lemma 39

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

/-- **Lemma 39** (p. 27). (i) There are a constant `C` and one deterministic program which, given a
connected multigraph on `Fin n` with positive integer capacities, `k ≥ 3`, `U = p/q > 0`, a root
`r` and `N` distinct `U`-medium rooted cuts each of shore size at most `k`, within
`k^(C k²) (N n + m + 1) (1 + log₂ n)^C` steps either outputs a k-cut of value at most `U`, or
outputs the certificate flag, and then `N ≤ D_k n` with `D_k = Sun(k, k + 1)(2^k + 1)`.
(ii) There is `C' > 0` with `D_k ≤ (C' k log k)^k` for every `k ≥ 3`. -/
theorem lemma_39 :
    (∃ C : ℕ, 1 ≤ C ∧ ∃ P : Program, IsDeterministic P ∧
      ∀ (n m k p q : ℕ) (r : Fin n) (N : ℕ) (ed : EdgeRecs n m) (S : ℕ → Finset (Fin n)),
        3 ≤ k → 0 < p → 0 < q → (∀ i, 0 < (ed i).2.2) → IsConnected (toGraph ed) →
        (∀ i j, i < N → j < N → S i = S j → i = j) →
        (∀ i, i < N → IsRootedCut r (S i) ∧ IsUMedium (toGraph ed) k ((p : ℝ) / q) (S i) ∧
          shoreSize (S i) ≤ k) →
        let T : ℝ := (k : ℝ) ^ (C * k ^ 2) * ((N : ℝ) * n + m + 1) * (1 + Real.logb 2 n) ^ C
        let inp := familyInput k p q r N ed S
        let W := wordSize C inp T
        ∀ ω : ℕ → Fin (2 ^ W), HaltsWithin W P inp ω T ∧
          (IsKCutAtMostOutput (toGraph ed) k ((p : ℝ) / q) (finalOutput W P inp ω) ∨
            (finalOutput W P inp ω = flagOut ∧ N ≤ Dk k * n))) ∧
    ∃ C' : ℝ, 0 < C' ∧ ∀ k : ℕ, 3 ≤ k → (Dk k : ℝ) ≤ (C' * k * Real.log k) ^ k := by sorry

end MinKCutII.Main
