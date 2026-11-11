-- Prove2me | Theorems.Thm_MinKCutII_Main_lemma_40
-- name    : MinKCutII.Main.lemma_40
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:40:39.634449+00:00
-- url     : https://prove2.me/theorems/06ce6792-1ce3-4a65-b45f-962d131a65cb
-- title:
--   Lemma 40 — Venn certificates: about k/2 medium cuts with enough atoms give a k-cut ≤ U, in O(kn + m) time and O(kn) space
-- statement:
--   Let $G$ be connected with positive capacities, $k\ge3$, $U>0$, and $S_0,\dots,S_{t-1}$ $U$-medium cuts; write $|\mathrm{At}(\cdot)|$ for the number of Venn atoms.
--
--   1. If $k$ is even, $t=k/2$ and $|\mathrm{At}(S_0,\dots,S_{t-1})|\ge k$, some $k$-cut constant on these atoms has value at most $U$.
--   2. If $k$ is odd and $t=r=(k+1)/2$: if $|\mathrm{At}(S_0,\dots,S_{r-2})|\ge k$, some $k$-cut constant on those atoms has value at most $U$; otherwise, if $|\mathrm{At}(S_0,\dots,S_{r-2})|=k-1$ and $|\mathrm{At}(S_0,\dots,S_{r-1})|\ge k+1$, some $k$-cut has value at most $U$.
--
--   Moreover there are a constant $C$ and one deterministic program which, given $U=p/q$ and the cuts by incidence vectors followed by the edge records, in each of these cases outputs such a $k$-cut within
--   $$C\,(kn+m+1)\ \text{steps, touching at most } C\,(kn+1)\ \text{memory cells.}$$
--   These certificates end the Venn-sequence phase of the overflow certificate.
--
--   Differences from the source:
--
--   - reading: an algorithm running in a given time (no machine model named) → a program of the published randomized word RAM DynConnWC.Program, words of C·⌈log₂(input magnitude + time bound)⌉ bits, input read once in order, output written as words; reason: the paper names no model; this is a standard unit-cost word RAM with Θ(log n)-bit words for fixed k
--   - encoding: the cuts given by their incidence vectors, and G → the words [n, m, k, p, q, t], the t incidence vectors, then the edge records; k-cut output as words 0, f(0), …, f(n−1); reason: a fixed layout; cuts first so that the edges can be scanned once
--   - encoding: deterministic algorithm → a program with no rand instruction (the statement is quantified over all tapes); reason: without rand the run does not depend on the tape
--   - encoding: a threshold U > 0 → U = p/q given by two positive integers; reason: an algorithm input is finite; every threshold the paper passes (kB/2) is rational
--   - generalization: capacities with total c(E) ≤ n^{O(1)} (§2 standing convention) → positive integer capacities of any size; reason: the word size grows with log c(E), so the bounded case is a special case
--   - generalization: a weighted multigraph (self-loops are discarded) → input records may be loops; reason: loops cross no cut, so a loopless input is a special case
--   - encoding: S_1, …, S_t (1-based) → S_0, …, S_{t−1}; the prefix S_1, …, S_{r−1} is the first t − 1 = r − 1 sets; reason: index base
--   - reading: k odd: S_1, …, S_t with r := (k+1)/2 → t = r: exactly the cuts S_1, …, S_r that the statement uses are given; reason: the proof notes t ≤ (k+1)/2; further cuts play no role
--   - reading: the atom partition contains a k-cut → a k-cut whose labelling is constant on the atoms (a k-part coarsening of the atom partition); reason: the proof merges atoms
--   - reading: O(kn) additional space → at most C·(k·n + 1) distinct memory cells touched; reason: the input is read once and is not in memory unless stored, so the touched cells are the working space
--   - encoding: O(kn + m) time and O(kn) additional space → C·(k·n + m + 1) steps and C·(k·n + 1) cells; reason: every O(·), Õ(·), k^{O(k²)} and log^{O(1)} is an explicit existentially quantified universal constant
--   - encoding: O(f) → C·(f + 1); reason: a program takes at least one step even when f = 0
--   - generalization: positive integer capacities (combinatorial part) → positive real capacities; reason: the combinatorial claims hold for real capacities; integers are a special case
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), pp. 27–28, Lemma 40

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_KCut
import Definitions.Def_MinKCutII_Main_Cuts
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MinKCutII_Main_Encoding

set_option autoImplicit false

open CombOpt.MinCut DynConnWC

namespace MinKCutII.Main

/-- **Lemma 40** (pp. 27–28). Combinatorial part, for a connected graph with positive capacities,
`k ≥ 3`, `U > 0` and `U`-medium cuts `S_0, …, S_{t−1}`:
1. `k` even, `t = k/2`, `|At(S_0, …, S_{t−1})| ≥ k`: some k-cut constant on the atoms has value `≤ U`;
2. `k` odd, `t = r = (k + 1)/2`: if `|At(S_0, …, S_{r−2})| ≥ k`, some k-cut constant on those atoms has
   value `≤ U`; if `|At(S_0, …, S_{r−2})| = k − 1` and `|At(S_0, …, S_{r−1})| ≥ k + 1`, some k-cut has
   value `≤ U`.
Algorithmic part: one deterministic program which, given the cuts by incidence vectors (then the
edge records), in each of these cases outputs such a k-cut within `C (k n + m + 1)` steps, touching
at most `C (k n + 1)` memory cells. -/
theorem lemma_40 :
    (∀ {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (G : CapGraph V E) (k : ℕ) (U : ℝ)
      (t : ℕ) (S : ℕ → Finset V),
      PosCap G → IsConnected G → 3 ≤ k → 0 < U →
      (∀ i, i < t → IsCut (S i) ∧ IsUMedium G k U (S i)) →
      (Even k → t = k / 2 → k ≤ numAtoms S t →
        ∃ f : V → Fin k, Function.Surjective f ∧ AtomConstant S t f ∧ partVal G f ≤ U) ∧
      (Odd k → t = (k + 1) / 2 → k ≤ numAtoms S (t - 1) →
        ∃ f : V → Fin k, Function.Surjective f ∧ AtomConstant S (t - 1) f ∧ partVal G f ≤ U) ∧
      (Odd k → t = (k + 1) / 2 → numAtoms S (t - 1) = k - 1 → k + 1 ≤ numAtoms S t →
        ∃ f : V → Fin k, Function.Surjective f ∧ partVal G f ≤ U)) ∧
    (∃ C : ℕ, 1 ≤ C ∧ ∃ P : Program, IsDeterministic P ∧
      ∀ (n m k p q t : ℕ) (ed : EdgeRecs n m) (S : ℕ → Finset (Fin n)),
        3 ≤ k → 0 < p → 0 < q → (∀ i, 0 < (ed i).2.2) → IsConnected (toGraph ed) →
        (∀ i, i < t → IsCut (S i) ∧ IsUMedium (toGraph ed) k ((p : ℝ) / q) (S i)) →
        ((Even k ∧ t = k / 2 ∧ k ≤ numAtoms S t) ∨
          (Odd k ∧ t = (k + 1) / 2 ∧ k ≤ numAtoms S (t - 1)) ∨
          (Odd k ∧ t = (k + 1) / 2 ∧ numAtoms S (t - 1) = k - 1 ∧ k + 1 ≤ numAtoms S t)) →
        let T : ℝ := (C : ℝ) * ((k : ℝ) * n + m + 1)
        let inp := vennInput k p q t ed S
        let W := wordSize C inp T
        ∀ ω : ℕ → Fin (2 ^ W), HaltsWithin W P inp ω T ∧
          SpaceWithin W P inp ω ((C : ℝ) * ((k : ℝ) * n + 1)) ∧
          ∃ f : Fin n → Fin k, Function.Surjective f ∧ partVal (toGraph ed) f ≤ (p : ℝ) / q ∧
            finalOutput W P inp ω = labelsOut f ∧
            (Even k → AtomConstant S t f) ∧
            (Odd k → k ≤ numAtoms S (t - 1) → AtomConstant S (t - 1) f)) := by sorry

end MinKCutII.Main
