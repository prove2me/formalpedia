-- Prove2me | Theorems.Thm_ManipPotential_lemma_6_2
-- name    : ManipPotential.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:53:19.514127+00:00
-- url     : https://prove2.me/theorems/abc44fc5-9163-475d-a479-48372aa10635
-- title:
--   Lemma 6.2 — an anonymous onto rule with $\mathrm{MP}\le K$ yields a rule $g$ on rational profiles with the three axioms
-- statement:
--   Let $m \ge 3$ and let $f$ be an anonymous and onto social choice function such that $\mathrm{MP}(f) \le K$ at every electorate size, and put $\lambda = K + 1$. Then there is a rule $g : \mathbb Q^{m!}_{\ge 0} \setminus \{0\} \to C$ satisfying:
--
--   1. **(Weighted) faithfulness:** $g(a\,r) = \mathrm{top}_r C$ for every ranking $r$ and every rational $a > 0$;
--   2. **Bounded manipulation potential:** for every background profile $P \in \mathbb Q^{m!}_{\ge 0}$, all rankings $r, s$ and positive rationals $a, b$ with $a \ge \lambda b$,
--   $$ g(P + a\,r) \succeq_r g(P + b\,s); \qquad (5) $$
--   3. **Conditional participation:** for every profile $P$, ranking $r$ and rational $a > 0$, if $P_r > 0$ then $g(P + a\,r) \succeq_r g(P)$.
--
--   This transfers the integer manipulation-potential bound of $f$ to a rule on rational profiles; every later step of the proof of Theorem 6.1 works with such a $g$.
--
--   Differences from the source:
--   - reading: "MP(f) ≤ K uniformly over all electorate sizes", with Section 2's standing n ≥ 2 → MP(f) ≤ K at every electorate size n (n = 1 included; n = 0 is vacuous); reason: footnote 8 (p.8) puts SCFs on profiles with any number of voters and the proof of Lemma 6.2 uses one-voter profiles; the n ≥ 2 reading is false for m ≥ 4 (top choice on one-voter profiles, Borda on {c₁, c₂, c₃} otherwise, has K = 1)
--   - reading: onto: each c wins at some profile → each c wins at some nonempty profile; reason: a profile has voters N = [n]; with the empty list allowed the statement is false (f([]) = c_m, three-candidate Borda elsewhere)
--   - encoding: g : ℚ^{m!}_{≥0} \ {0} → C → a total g : (Ranking m → ℚ) → Fin m, queried (here and in the axioms) only at nonnegative nonzero vectors; reason: Lean convention; values outside the domain never matter
--   - encoding: profiles ≻_N ∈ L(C)^n, rankings as relations, MP ∈ ℤ_{≥0} ∪ {∞} → List (Ranking m) with rankings as permutations to positions, MP in ℕ∞; reason: Lean convention; same instances
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.2, p.26

import Mathlib
import Definitions.Def_ManipPotential_Anonymous
import Definitions.Def_ManipPotential_Onto
import Definitions.Def_ManipPotential_manipPotentialAt
import Definitions.Def_ManipPotential_GAxioms

namespace ManipPotential

/-- Lemma 6.2 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.2, p.26): under the assumptions of Theorem 6.1, with `λ = K + 1`,
there is a rule `g` on rational profiles satisfying weighted faithfulness, bounded manipulation
potential (5) and conditional participation. -/
theorem lemma_6_2 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (f : List (Ranking m) → Fin m)
    (hA : Anonymous f) (hO : Onto f) (K : ℕ) (hK : ∀ n : ℕ, manipPotentialAt f n ≤ K) :
    ∃ g : (Ranking m → ℚ) → Fin m, GAxioms K g := by sorry

end ManipPotential
