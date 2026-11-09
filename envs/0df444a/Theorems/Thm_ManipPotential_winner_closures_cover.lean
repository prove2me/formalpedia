-- Prove2me | Theorems.Thm_ManipPotential_winner_closures_cover
-- name    : ManipPotential.winner_closures_cover
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:55:11.175482+00:00
-- url     : https://prove2.me/theorems/67e84059-73fc-41e3-a98c-daa8de6e2f93
-- title:
--   Section 6, after (12) — the winner closures $A_j$ cover $\Omega$, and (11) holds on each $A_j$
-- statement:
--   Let $m \ge 3$, $\lambda = K + 1$, $\delta = (m-2)/(\lambda^6 + m - 2)$, and let $g$ satisfy the axioms of Lemma 6.2. With $\Omega = \mathbb R^{m!}_{>0}$ and $A_j = \mathrm{cl}_\Omega\{P \in \Omega \cap \mathbb Q^{m!} : g(P) = c_j\}$:
--
--   1. the sets $A_1, \dots, A_m$ cover $\Omega$: $\Omega \subseteq \bigcup_j A_j$;
--   2. inequality (11) holds throughout $A_j$: for every $j$ and every real profile $P = (x, y) \in A_j$,
--   $$ x_j \ \ge\ \delta \sum_{i=1}^m x_i - \lambda(1 - \delta)\, \|y\|_1 . $$
--
--   These are the two properties of the winner closures used to apply Sperner's lemma in Proposition 6.11.
--
--   Differences from the source:
--   - generalization: g is the rule on rational profiles constructed from f in Lemma 6.2 → any g satisfying the three axioms of Lemma 6.2 with λ = K + 1; reason: the proof uses only these axioms, and the g of Lemma 6.2 satisfies them
--   - generalization: λ > 1, a standing assumption from the remark after Lemma 6.6 (p.30, "for the rest of the proof, we can assume λ > 1") → no λ > 1 hypothesis: every K ∈ ℕ, so λ = K + 1 ≥ 1; reason: at K = 0 no g satisfies the axioms (remark after Lemma 6.6, item lambda_one_impossible), so the extra instances are vacuous and the statement specializes to the source
--   - encoding: g : ℚ^{m!}_{≥0} \ {0} → C → a total g : (Ranking m → ℚ) → Fin m, queried (here and in the axioms) only at nonnegative nonzero vectors; reason: Lean convention; values outside the domain never matter
--   - encoding: closure relative to Ω, real profiles as vectors in ℝ^{m!} → Ω ∩ closure in ℝ^{L(C)} (product topology) of the cast rational profiles; reason: equal sets
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, "Common junctions and Sperner's lemma", after Eq. (12), p.30

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_winnerClosure
import Definitions.Def_ManipPotential_cycTotal
import Definitions.Def_ManipPotential_extNorm
import Definitions.Def_ManipPotential_delta

namespace ManipPotential

/-- The sets `A_j` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, "Common junctions and Sperner's lemma", after Eq. (12), p.30):
`{A_j}_j` covers `Ω`, and inequality (11) `x_j ≥ δ X − λ(1 − δ)‖y‖₁` holds throughout `A_j`. -/
theorem winner_closures_cover {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) :
    Omega m ⊆ ⋃ j, winnerClosure g j ∧
    ∀ (j : Fin m), ∀ P ∈ winnerClosure g j,
      (delta m K : ℝ) * cycTotal P - ((K : ℝ) + 1) * (1 - (delta m K : ℝ)) * extNorm P ≤
        P (ell j) := by sorry

end ManipPotential
