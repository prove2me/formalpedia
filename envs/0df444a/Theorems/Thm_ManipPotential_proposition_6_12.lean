-- Prove2me | Theorems.Thm_ManipPotential_proposition_6_12
-- name    : ManipPotential.proposition_6_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:55:05.388082+00:00
-- url     : https://prove2.me/theorems/ffb17b43-79c7-48fb-bfcc-f026b6a650b6
-- title:
--   Proposition 6.12 — comparison vectors in a common $(m-1)$-dimensional space
-- statement:
--   Let $m \ge 3$, $\lambda = K + 1$, and let $g$ satisfy the axioms of Lemma 6.2. There is a linear subspace $W \subseteq \mathbb R^{m!}$ of dimension $m - 1$ such that for every pair of distinct indices $i, j \in [m]$ there is a vector $w_{ij}$ with
--   $$
--   w_{ij} \in W \cap C_{ij}, \qquad w_{ij} \cdot (\ell_i - \ell_j) = 1 .
--   $$
--   The subspace $W$ is fixed before the pair $(i, j)$ is chosen; $C_{ij}$ is the comparison cone (18)–(19) with constant $\lambda$, and $\ell_i, \ell_j$ denote unit vectors.
--
--   Differences from the source:
--   - generalization: g is the rule on rational profiles constructed from f in Lemma 6.2 → any g satisfying the three axioms of Lemma 6.2 with λ = K + 1; reason: the proof uses only these axioms, and the g of Lemma 6.2 satisfies them
--   - generalization: λ > 1, a standing assumption from the remark after Lemma 6.6 (p.30, "for the rest of the proof, we can assume λ > 1") → no λ > 1 hypothesis: every K ∈ ℕ, so λ = K + 1 ≥ 1; reason: at K = 0 no g satisfies the axioms (remark after Lemma 6.6, item lambda_one_impossible), so the extra instances are vacuous and the statement specializes to the source
--   - encoding: g : ℚ^{m!}_{≥0} \ {0} → C → a total g : (Ranking m → ℚ) → Fin m, queried (here and in the axioms) only at nonnegative nonzero vectors; reason: Lean convention; values outside the domain never matter
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Proposition 6.12, p.35

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_Cmp
import Definitions.Def_ManipPotential_ell
import Definitions.Def_ManipPotential_unitVec

namespace ManipPotential

/-- Proposition 6.12 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Proposition 6.12, p.35), with `λ = K + 1`: there is a linear subspace
`W ⊆ ℝ^{m!}` of dimension `m − 1` such that for every pair of distinct indices `i, j` there is a
vector `w_ij ∈ W ∩ C_ij` with `w_ij · (ℓ_i − ℓ_j) = 1`. The subspace is chosen before the pair. -/
theorem proposition_6_12 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) :
    ∃ W : Submodule ℝ (Ranking m → ℝ), Module.finrank ℝ W = m - 1 ∧
      ∀ i j : Fin m, i ≠ j → ∃ w ∈ W, w ∈ Cmp ((K : ℝ) + 1) i j ∧
        dotProduct w (unitVec (ell i) - unitVec (ell j)) = 1 := by sorry

end ManipPotential
