-- Prove2me | Theorems.Thm_MalleableSched_Supplement_theorem_14
-- name    : MalleableSched.Supplement.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:41:32.793335+00:00
-- url     : https://prove2.me/theorems/23ae83a8-6b4d-5d95-a8c3-7244919ab478
-- title:
--   Theorem 14 — Step 3b: a well-structured assignment with maximum load at most $5C$
-- statement:
--   Work in the setting of Theorem 13: matroids $\mathcal F_j$ with ranks $r_j$, quotas $q_j>0$, speeds $g_j=r_j/q_j$, a target $C>0$, $t_j=\lceil q_j/C\rceil$, $J_1=\{j:t_j=1\}$, $J_2=J\setminus J_1$, Step 1's $\mathbf S^1$ (each $j\in J_1$ on one machine $i^1_j$, load at most $2C$ per machine) and Step 2's $B\in\mathcal F'\cap\mathcal F''$ with $|B|=\sum_{j\in J_2}t_j$. For each machine $i$ let $e_i=\{j\in J_2:(i,j)\in B\}$; the non-empty $e_i$ are the edges (loops when $|e_i|=1$) of a multigraph on $J_2$.
--
--   1. There is an orientation of this multigraph, given by a head $j_i\in e_i$ for every $i$ with $e_i\neq\emptyset$, in which every $j\in J_2$ is the head of at least $\lfloor t_j/2\rfloor$ edges.
--   2. For every such orientation, the assignment $\mathbf T$ with $T_j=\{i^1_j\}$ for $j\in J_1$ and $T_j=\bar S^2_j=\{i:e_i\neq\emptyset,\ j_i=j\}$ for $j\in J_2$ is an assignment, is well-structured, and satisfies
--   $$
--   L(\mathbf T)\le 5C.
--   $$
--
--   This is the second half of the paper's Theorem 10: a well-structured assignment can be scheduled with makespan equal to its maximum load, which gives the 5-approximation for Scheduling.
--
--   **Formalization Note** The orientation is encoded by an optional head map $h:M\to J\cup\{\mathrm{none}\}$ with $h(i)=j_i\in e_i$ whenever $e_i\ne\emptyset$. This represents exactly the paper's heads on non-empty edges and remains total when the job set is empty. Loads take values in $[0,\infty]$, with $f_j(S)=\infty$ when $r_j(S)=0$.
--
--   Differences from the source:
--   - reading: quota q_j ∈ ℝ≥0 and g_j = r_j/q_j → q_j > 0; reason: r_j/q_j is undefined at q_j = 0, and p.4 defines a scaled matroid rank as α·r with α > 0, so q_j = 1/α > 0
--   - generalization: S¹ is the assignment obtained by the rounding algorithm of Lenstra et al. from (LP2) → any S¹ putting each job of J1 on one machine with load at most 2C on every machine; reason: the paper uses only these two properties of S¹ (p.11, proof on p.13); the rounded solution is one such S¹
--   - encoding: B a maximum cardinality common independent set of F′ ∩ F″ with |B| ≥ Σ_{j∈J2} t_j (the algorithm did not stop) → B ∈ F′ ∩ F″ with |B| = Σ_{j∈J2} t_j; reason: every member of F′ has at most Σ_{j∈J2} t_j elements, so the two conditions coincide
--   - reading: E := {e_i : i ∈ M, e_i ≠ ∅} written as a set, followed by an edge and head for every machine i → non-empty edges are indexed by machines, so equal e_i remain parallel edges; reason: otherwise equal sets would collapse, contradicting the stated degree t_j and the later definition B̄ := {(i,j_i)}
--   - encoding: a head j_i ∈ e_i for every non-empty edge e_i → an optional head map h : M → Option J that is some j_i ∈ e_i on every non-empty edge; reason: this is the same orientation data and does not require the job type to be non-empty when every edge is empty
--   - generalization: "it constructs" the assignment from the orientation D computed by Hakimi's method → the existence of an orientation with every in-degree ≥ ⌊t_j/2⌋, and the conclusion for every such orientation; reason: the proof uses only the in-degree bound of D (p.12), so it covers the orientation the algorithm computes
--   - encoding: real loads, f_j(S) = q_j/r_j(S) → loads in [0, ∞] with f_j(S) = ∞ when r_j(S) = 0; reason: the paper's f_j(∅) = ∞ convention (p.3); the bound 5C is finite, so it excludes infinite loads exactly as the real statement does
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, Theorem 14, p.13; setting §3 p.10, Steps 1–2 §3.1 p.11, Step 3b §3.1 p.12

import Mathlib
import Definitions.Def_MalleableSched_Model
import Definitions.Def_MalleableSched_Supplement_ScaledMatroid

open scoped ENNReal

namespace MalleableSched.Supplement

/-- **Theorem 14 (Step 3b: a well-structured assignment with maximum load at most 5C).**
Fotakis, Matuschke & Papadigenopoulos, *Assigning and Scheduling Generalized Malleable Jobs under
Subadditive or Submodular Processing Speeds*, arXiv:2111.06225v2, Theorem 14, p.13: "If the
algorithm reaches Step 3b, it constructs a well-structured assignment with maximum machine load at
most 5C."

Setting as in Theorem 13 (§3, pp.10–11): matroids `F_j`, quotas `q_j > 0`, speeds
`g_j = r_j/q_j`, target `C > 0`, `t_j = ⌈q_j/C⌉`, `J1 = {t_j = 1}`, `J2 = J \ J1`, Step 1's `S¹`
and Step 2's `B`. Step 3b (p.12) orients the multigraph on `J2` with one edge
`e_i = {j : (i, j) ∈ B}` per machine `i` with `e_i ≠ ∅` so that every `j ∈ J2` has in-degree at
least `⌊t_j/2⌋`, and returns `S¹` on `J1` and `S̄²_j = {i : e_i ≠ ∅, head of e_i = j}` on `J2`.

The statement has two parts:
1. such an orientation exists;
2. for every such orientation, the returned assignment is an assignment, is well-structured, and
   has maximum load at most `5C`.

**Formalization Note.** An orientation is an optional head map `h : Fin m → Option (Fin n)` with
`h i = some j` for a `j ∈ e_i` whenever `e_i` is non-empty (`IsStep3bOrientation`). This directly
encodes that the paper chooses heads only for non-empty edges and includes the empty job set. Loads
are in `ℝ≥0∞` with `f_j(S) = q_j / r_j(S)` (`∞` when `r_j(S) = 0`); `q_j > 0` is assumed as in
Theorem 13. -/
theorem theorem_14 {n m : ℕ} (F : Fin n → Finset (Finset (Fin m))) (hF : ∀ j, IsMatroid (F j))
    (q : Fin n → ℝ) (hq : ∀ j, 0 < q j) (C : ℝ) (hC : 0 < C)
    (i1 : Fin n → Fin m) (h1 : IsStep1Output (matroidSpeed F q) (quotaCount q C) i1 C)
    (B : Finset (Fin m × Fin n)) (hB : IsStep2Output F (quotaCount q C) B) :
    (∃ h : Fin m → Option (Fin n), IsStep3bOrientation (quotaCount q C) B h) ∧
      ∀ h : Fin m → Option (Fin n), IsStep3bOrientation (quotaCount q C) B h →
        IsAssignment (step3bAssignment (quotaCount q C) i1 B h) ∧
          WellStructured (step3bAssignment (quotaCount q C) i1 B h) ∧
          maxLoad (matroidSpeed F q) (step3bAssignment (quotaCount q C) i1 B h) ≤
            ENNReal.ofReal (5 * C) := by sorry

end MalleableSched.Supplement
