-- Prove2me | Theorems.Thm_MultiwayCut_observation_5_1
-- name    : MultiwayCut.observation_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:35.944919+00:00
-- url     : https://prove2.me/theorems/031a71bf-8f93-4792-8270-bf69d0df6dd0
-- title:
--   Observation 5.1 — the matrix (5.3) satisfies Lemma 5.1, $a_j=a_5$ for $j\ge5$, and $a_1\succeq a_2\succeq a_3\succeq a_5\succeq a_4\succeq0$
-- statement:
--   Let $A$ be the matrix (5.3) and $\mathbf a_j$ its $j$-th row. Then $A$ is symmetric and satisfies the three conditions of Lemma 5.1. Moreover, when $k\ge5$:
--   1. $\mathbf a_j=\mathbf a_5$ for all $j\ge5$;
--   2. $\mathbf a_1\succeq\mathbf a_2\succeq\mathbf a_3\succeq\mathbf a_5\succeq\mathbf a_4\succeq0$.
--
--   These are the facts about (5.3) that the case analysis of Lemma 5.4 uses.
--
--   Differences from the source:
--   - encoding: the paper's coordinates and terminals $1,\dots,k$, $1/\ell$ → `Fin k` from $0$, $1/(\ell+1)$; reason: Lean convention; the same statement after the index shift
--   - reading: the matrix (5.3) printed with "…" for a general $k$ → `A53 k` for every $k\ge1$, defined by the entry formula (the top-left $k\times k$ block of the printed pattern); reason: the paper never restricts $k$; this is the only matrix consistent with the printed pattern
--   - reading: clauses 1–2, which mention $\mathbf a_5$ → stated for $k\ge5$; reason: the row $\mathbf a_5$ exists only when $k\ge5$
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, Observation 5.1, p.8

import Mathlib
import Definitions.Def_MultiwayCut_Transformation
import Definitions.Def_MultiwayCut_A53

namespace MultiwayCut

/-- **Observation 5.1**, Buchbinder, Schwartz & Weizman, *Simplex Transformations and the
Multiway Cut Problem*, manuscript of Nov. 1, 2016, p.8: the matrix `A` of (5.3) satisfies the
conditions in Lemma 5.1 (it is symmetric and satisfies conditions 1–3), and:
1. `a_j = a₅` for all `j ≥ 5`;
2. `a₁ ⪰ a₂ ⪰ a₃ ⪰ a₅ ⪰ a₄ ⪰ 0`.

**Formalization Note.** 0-based rows: `a₁, a₂, a₃, a₄, a₅` are `A53 k 0, 1, 2, 3, 4`. The
conditions of Lemma 5.1 are stated for every `k ≥ 1`; clauses 1 and 2 mention `a₅`, so they are
stated for `k ≥ 5`. -/
theorem observation_5_1 {k : ℕ} [NeZero k] :
    ((A53 k).IsSymm ∧ Lemma51Conditions (A53 k)) ∧
    ∀ hk : 5 ≤ k,
      (∀ j : Fin k, 4 ≤ j.val → A53 k j = A53 k ⟨4, by omega⟩) ∧
      PrefixGe (A53 k ⟨0, by omega⟩) (A53 k ⟨1, by omega⟩) ∧
      PrefixGe (A53 k ⟨1, by omega⟩) (A53 k ⟨2, by omega⟩) ∧
      PrefixGe (A53 k ⟨2, by omega⟩) (A53 k ⟨4, by omega⟩) ∧
      PrefixGe (A53 k ⟨4, by omega⟩) (A53 k ⟨3, by omega⟩) ∧
      PrefixGe (A53 k ⟨3, by omega⟩) 0 := by sorry

end MultiwayCut
