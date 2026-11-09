-- Prove2me | Theorems.Thm_ManipPotential_lemma_6_5
-- name    : ManipPotential.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:53:07.430048+00:00
-- url     : https://prove2.me/theorems/0a6724b7-9e3a-444d-b786-9182baf566bf
-- title:
--   Lemma 6.5 — L- and R-compressions
-- statement:
--   Let $m \ge 3$, $\lambda = K + 1$, and let $g$ satisfy the axioms of Lemma 6.2.
--
--   1. **(L-Compression)** For every $x \in \mathbb Q^m_{\ge 0} \setminus \{0\}$ with $X = \sum_{j=1}^m x_j > 0$,
--   $$ g(xL) = c_j \ \Longrightarrow\ g\Big(x_j \ell_j + \frac{X - x_j}{\lambda}\, \ell_{j+1}\Big) = c_j. $$
--   2. **(R-Compression)** For distinct $i, j \in [m]$ and positive rationals $x_i, x_j$,
--   $$ g(x_i r_i + x_j r_j) = c_i \ \Longrightarrow\ g\Big(\lambda x_i \ell_i + \frac{x_j}{\lambda}\, \ell_{i-1}\Big) = c_i. $$
--
--   Indices are taken modulo $m$. The compressions reduce any L-profile, or any binary R-profile, to a binary L-profile on adjacent indices with the same winner.
--
--   Differences from the source:
--   - generalization: g is the rule on rational profiles constructed from f in Lemma 6.2 → any g satisfying the three axioms of Lemma 6.2 with λ = K + 1; reason: the proof uses only these axioms, and the g of Lemma 6.2 satisfies them
--   - encoding: g : ℚ^{m!}_{≥0} \ {0} → C → a total g : (Ranking m → ℚ) → Fin m, queried (here and in the axioms) only at nonnegative nonzero vectors; reason: Lean convention; values outside the domain never matter
--   - encoding: candidates c_1…c_m, indices mod m, ℓ_j and r_j as printed → Fin m (0-based), ℓ_j : c ↦ j − c and r_j : c ↦ c − j as permutations to positions; reason: Lean convention; same rankings
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.5, p.28

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_cycL
import Definitions.Def_ManipPotential_rr

namespace ManipPotential

/-- Lemma 6.5 (cyclic compressions) (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.5, p.28), with `λ = K + 1`:
(L-Compression) for `x ∈ ℚ^m_{≥0} \ {0}` and `X = ∑_j x_j`,
`g(xL) = c_j ⟹ g(x_j ℓ_j + ((X − x_j)/λ) ℓ_{j+1}) = c_j`;
(R-Compression) for distinct `i, j` and positive rationals `x_i, x_j`,
`g(x_i r_i + x_j r_j) = c_i ⟹ g(λ x_i ℓ_i + (x_j/λ) ℓ_{i−1}) = c_i`. -/
theorem lemma_6_5 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) :
    (∀ x : Fin m → ℚ, 0 ≤ x → x ≠ 0 → ∀ j : Fin m, g (cycL x) = j →
      g (x j • unitVec (ell j) +
        (((∑ i, x i) - x j) / ((K : ℚ) + 1)) • unitVec (ell (j + 1))) = j) ∧
    (∀ i j : Fin m, i ≠ j → ∀ xi xj : ℚ, 0 < xi → 0 < xj →
      g (xi • unitVec (rr i) + xj • unitVec (rr j)) = i →
      g ((((K : ℚ) + 1) * xi) • unitVec (ell i) +
        (xj / ((K : ℚ) + 1)) • unitVec (ell (i - 1))) = i) := by sorry

end ManipPotential
