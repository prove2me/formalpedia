-- Prove2me | Theorems.Thm_ManipPotential_corollary_6_4
-- name    : ManipPotential.corollary_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:52:57.043188+00:00
-- url     : https://prove2.me/theorems/03b0c931-9eaa-430d-aa71-d5a9006f63a2
-- title:
--   Corollary 6.4 — support of $g$ on purely cyclic profiles
-- statement:
--   Let $m \ge 3$ and let $g$ satisfy the axioms of Lemma 6.2 with $\lambda = K + 1$. For every $x \in \mathbb Q^m_{\ge 0} \setminus \{0\}$ with $S = \mathrm{supp}(x)$,
--   $$
--   g(xL) \in \{c_j : j \in S\} \quad\text{and}\quad g(xR) \in \{c_j : j \in S\}.
--   $$
--   On a purely cyclic profile the winner is the top candidate of a ranking present in the profile.
--
--   Differences from the source:
--   - generalization: g is the rule on rational profiles constructed from f in Lemma 6.2 → any g satisfying the three axioms of Lemma 6.2 with λ = K + 1; reason: the proof uses only these axioms, and the g of Lemma 6.2 satisfies them
--   - encoding: g : ℚ^{m!}_{≥0} \ {0} → C → a total g : (Ranking m → ℚ) → Fin m, queried (here and in the axioms) only at nonnegative nonzero vectors; reason: Lean convention; values outside the domain never matter
--   - encoding: candidates c_1…c_m, indices mod m, ℓ_j and r_j as printed → Fin m (0-based), ℓ_j : c ↦ j − c and r_j : c ↦ c − j as permutations to positions; reason: Lean convention; same rankings
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Corollary 6.4, p.28

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_cycL
import Definitions.Def_ManipPotential_cycR
import Definitions.Def_ManipPotential_supp

namespace ManipPotential

/-- Corollary 6.4 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Corollary 6.4, p.28): for every `x ∈ ℚ^m_{≥0} \ {0}` with
`S = supp(x)`, `g(xL) ∈ {c_j : j ∈ S}` and `g(xR) ∈ {c_j : j ∈ S}`. -/
theorem corollary_6_4 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) (x : Fin m → ℚ) (hx : 0 ≤ x) (hx0 : x ≠ 0) :
    g (cycL x) ∈ supp x ∧ g (cycR x) ∈ supp x := by sorry

end ManipPotential
