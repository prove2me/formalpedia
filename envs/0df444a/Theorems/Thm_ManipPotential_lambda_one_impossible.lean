-- Prove2me | Theorems.Thm_ManipPotential_lambda_one_impossible
-- name    : ManipPotential.lambda_one_impossible
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:56:10.205407+00:00
-- url     : https://prove2.me/theorems/bb788aed-8c66-4f05-9738-aa20ae68446d
-- title:
--   Section 6, remark after Lemma 6.6 — $\lambda = 1$ ($K = 0$) is impossible
-- statement:
--   Let $m \ge 3$. There is no rule $g$ on rational profiles satisfying the three axioms of Lemma 6.2 with $K = 0$, i.e. with $\lambda = 1$.
--
--   Indeed, on the equal-weight L-profile every index has share $1/m$, while (9) of Lemma 6.6 would require the winner's share to be at least $\delta = (m-2)/(m-1) > 1/m$. This recovers the Gibbard–Satterthwaite impossibility in the present framework and justifies assuming $\lambda > 1$ for the rest of the proof.
--
--   Differences from the source:
--   - generalization: the g of Lemma 6.2 cannot exist with λ = 1 → no g whatsoever satisfies the three axioms with K = 0; reason: the remark's argument uses only the axioms (through Lemma 6.6)
--   - encoding: g : ℚ^{m!}_{≥0} \ {0} → C → a total g : (Ranking m → ℚ) → Fin m, queried (here and in the axioms) only at nonnegative nonzero vectors; reason: Lean convention; values outside the domain never matter
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, remark after Lemma 6.6, p.30

import Mathlib
import Definitions.Def_ManipPotential_GAxioms

namespace ManipPotential

/-- `λ = 1` is impossible (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, remark after Lemma 6.6, p.30): for `m ≥ 3` no rule on
rational profiles satisfies the axioms of Lemma 6.2 with `K = 0` (Gibbard–Satterthwaite). -/
theorem lambda_one_impossible {m : ℕ} [NeZero m] (hm : 3 ≤ m) :
    ¬ ∃ g : (Ranking m → ℚ) → Fin m, GAxioms 0 g := by sorry

end ManipPotential
