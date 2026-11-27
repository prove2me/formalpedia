-- Prove2me | Theorems.Thm_MalleableSched_Supplement_theorem_13
-- name    : MalleableSched.Supplement.theorem_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:40:43.237033+00:00
-- url     : https://prove2.me/theorems/a0c5439c-d312-41db-9ef3-e55828f90615
-- title:
--   Theorem 13 — Step 3a: the merged assignment has maximum load at most $4C$
-- statement:
--   Let every job $j$ have a matroid $\mathcal F_j$ on the machine set $M$ with rank $r_j$ and a quota $q_j>0$, and speed $g_j=r_j/q_j$, so that $f_j(S)=q_j/r_j(S)$. Fix a target load $C>0$, let $t_j=\lceil q_j/C\rceil$, $J_1=\{j:t_j=1\}$ and $J_2=J\setminus J_1$. Suppose the algorithm of §3 reaches Step 3a, that is:
--
--   1. Step 1 produced $\mathbf S^1$: each $j\in J_1$ on a single machine $i^1_j$, with $\sum_{j\in J_1:\,i^1_j=i}f_j(\{i\})\le2C$ for every machine $i$;
--   2. Step 2 produced $B\in\mathcal F'\cap\mathcal F''$ with $|B|=\sum_{j\in J_2}t_j$.
--
--   Let $\mathbf S$ be the merged assignment: $S_j=\{i^1_j\}$ for $j\in J_1$ and $S_j=\{i:(i,j)\in B\}$ for $j\in J_2$. Then $\mathbf S$ is an assignment (every $S_j$ is non-empty) and
--
--   $$
--   L(\mathbf S)=\max_{i\in M}\sum_{j:\,i\in S_j}f_j(S_j)\le 4C.
--   $$
--
--   This is the first half of the paper's Theorem 10: the decision procedure either certifies that no assignment of maximum load $C$ exists or produces one of maximum load at most $4C$.
--
--   **Formalization Note** Processing times and loads take values in $[0,\infty]$, with $f_j(S)=\infty$ when $r_j(S)=0$. Step 1's and Step 2's outputs enter as hypotheses (see the definition `MalleableSched.Supplement.ScaledMatroid`).
--
--   Differences from the source:
--   - reading: quota q_j ∈ ℝ≥0 and g_j = r_j/q_j → q_j > 0; reason: r_j/q_j is undefined at q_j = 0, and p.4 defines a scaled matroid rank as α·r with α > 0, so q_j = 1/α > 0
--   - generalization: S¹ is the assignment obtained by the rounding algorithm of Lenstra et al. from (LP2) → any S¹ putting each job of J1 on one machine with load at most 2C on every machine; reason: the paper uses only these two properties of S¹ (p.11, proof on p.13); the rounded solution is one such S¹
--   - encoding: B a maximum cardinality common independent set of F′ ∩ F″ with |B| ≥ Σ_{j∈J2} t_j (the algorithm did not stop) → B ∈ F′ ∩ F″ with |B| = Σ_{j∈J2} t_j; reason: every member of F′ has at most Σ_{j∈J2} t_j elements, so the two conditions coincide
--   - encoding: real loads, f_j(S) = q_j/r_j(S) → loads in [0, ∞] with f_j(S) = ∞ when r_j(S) = 0; reason: the paper's f_j(∅) = ∞ convention (p.3); the bound 4C is finite, so it excludes infinite loads exactly as the real statement does
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, Theorem 13, p.13; setting §3 p.10 and Steps 1, 2, 3a §3.1 p.11

import Mathlib
import Definitions.Def_MalleableSched_Model
import Definitions.Def_MalleableSched_Supplement_ScaledMatroid

open scoped ENNReal

namespace MalleableSched.Supplement

/-- **Theorem 13 (Step 3a: the merged assignment has maximum load at most 4C).**
Fotakis, Matuschke & Papadigenopoulos, *Assigning and Scheduling Generalized Malleable Jobs under
Subadditive or Submodular Processing Speeds*, arXiv:2111.06225v2, Theorem 13, p.13: "If the
algorithm reaches Step 3a, it constructs an assignment of maximum machine load at most 4C."

Setting (§3, pp.10–11): every job `j` has a matroid `F_j` on the machines and a quota `q_j > 0`,
with speed `g_j(S) = r_j(S)/q_j`; `C > 0` is the target load, `t_j = ⌈q_j/C⌉`,
`J1 = {j : t_j = 1}`, `J2 = J \ J1`. "The algorithm reaches Step 3a" means Step 1 produced `S¹`
(single machines `i1 j` for `j ∈ J1`, load at most `2C`) and Step 2 produced `B ∈ F′ ∩ F″` with
`|B| = Σ_{j∈J2} t_j`. The constructed assignment is `S¹` on `J1` and `S²_j = {i : (i, j) ∈ B}` on
`J2`.

**Formalization Note.** Jobs `Fin n`, machines `Fin m`; processing times and loads are in `ℝ≥0∞`
(`procTime`, `maxLoad` of the base model), so `f_j(S) = q_j / r_j(S)` and `= ∞` when `r_j(S) = 0`.
`q_j > 0` is assumed (the paper writes `q_j ∈ ℝ≥0`, but `r_j/q_j` is a scaled matroid rank only for
`q_j > 0`). Step 1's and Step 2's outputs are hypotheses (`IsStep1Output`, `IsStep2Output`); any
`S¹` with load at most `2C` is admitted. -/
theorem theorem_13 {n m : ℕ} (F : Fin n → Finset (Finset (Fin m))) (hF : ∀ j, IsMatroid (F j))
    (q : Fin n → ℝ) (hq : ∀ j, 0 < q j) (C : ℝ) (hC : 0 < C)
    (i1 : Fin n → Fin m) (h1 : IsStep1Output (matroidSpeed F q) (quotaCount q C) i1 C)
    (B : Finset (Fin m × Fin n)) (hB : IsStep2Output F (quotaCount q C) B) :
    IsAssignment (step3aAssignment (quotaCount q C) i1 B) ∧
      maxLoad (matroidSpeed F q) (step3aAssignment (quotaCount q C) i1 B) ≤
        ENNReal.ofReal (4 * C) := by sorry

end MalleableSched.Supplement
