-- Prove2me | Theorems.Thm_LIPAlgorithm_lemma_3_5
-- name    : LIPAlgorithm.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:01.260111+00:00
-- url     : https://prove2.me/theorems/9a458b01-cc5e-4164-95bb-5ef76adbd200
-- title:
--   Lemma 3.5 — zero-slack exchange
-- statement:
--   Let $L$ be a rank-$n$ well-rounded lattice, $A=\mathrm{Min}(L)$, $1\le j\le n$. If rank $j$ is ambiguous at $w$ and $B$ is an independent $j$-set with $p_B\in F_j(w)$, there exist $b\in B$ and $x\in A\setminus B$ such that $B-b+x$ is independent and
--
--   $$\langle w,b-x\rangle=0.$$
--
--   This certificate of ambiguity is what makes the resolved ranks computable.
--
--   Differences from the source:
--   - generalization: w ∈ L* (Definition 3.2) → every w ∈ ℝⁿ; reason: the proof does not use w ∈ L*, and L* ⊂ ℝⁿ, so the source's claim is the restriction
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Lemma 3.5, p.19

import Mathlib
import Definitions.Def_LIPAlgorithm_Resolved

namespace LIPAlgorithm

/-- **Lemma 3.5 (Zero-slack exchange).** Aggarwal, Jiang, Li, Liu, STOC 2027 submission (manuscript sha256 61ee52aa…),
Lemma 3.5, p.19 (PDF p.22). If rank `j` is ambiguous at `w` and `B` is an independent `j`-set with `p_B ∈ F_j(w)`, there are
`b ∈ B` and `x ∈ A ∖ B` with `B − b + x` independent and `⟨w, b − x⟩ = 0`.

**Formalization Note.** `w` ranges over `ℝⁿ`, which contains `L*`. The set `B − b + x` is the Finset `B'` with the stated
underlying set; its membership in `indepSets L j` includes independence and size `j`. -/
theorem lemma_3_5 {n : ℕ} (L : Submodule ℤ (E n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : IsWellRounded L) (j : ℕ) (hj₁ : 1 ≤ j) (hj₂ : j ≤ n) (w : E n)
    (hamb : Ambiguous L j w) (B : Finset (E n)) (hB : B ∈ indepSets L j)
    (hpB : pSum B ∈ faceF L j w) :
    ∃ b ∈ B, ∃ x ∈ minShell L, x ∉ B ∧
      (∃ B' ∈ indepSets L j, (B' : Set (E n)) = insert x ((B : Set (E n)) \ {b})) ∧
      inner ℝ w (b - x) = 0 := by sorry

end LIPAlgorithm
