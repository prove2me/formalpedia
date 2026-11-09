-- Prove2me | Theorems.Thm_ManipPotential_theorem_6_1
-- name    : ManipPotential.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:47:42.930809+00:00
-- url     : https://prove2.me/theorems/d322bb73-5182-4bd0-9e8a-213ed886b48c
-- title:
--   Theorem 6.1 — an anonymous onto rule with $\mathrm{MP}(f)\le K$ at every electorate size has $K \ge m-2$
-- statement:
--   Let $f$ be an anonymous and onto social choice function on $m$ candidates. If there is an integer $K \ge 0$, possibly depending on $m$ but independent of $n$, such that
--   $$
--   \mathrm{MP}(f) \le K \quad \text{at every electorate size } n,
--   $$
--   then
--   $$
--   K \ \ge\ m - 2 .
--   $$
--
--   Borda Count attains $\mathrm{MP} = m - 2$ at every electorate size (Theorem 4.4), so the bound is tight: among anonymous onto rules, no rule has an $n$-independent manipulation potential below that of Borda Count. For $K = 0$ this contains the Gibbard–Satterthwaite impossibility for anonymous onto rules.
--
--   **Formalization Note** The conclusion is written $m \le K + 2$, which is $K \ge m - 2$ without truncated subtraction.
--
--   Differences from the source:
--   - reading: "MP(f) ≤ K uniformly over all electorate sizes", with Section 2's standing n ≥ 2 → MP(f) ≤ K at every electorate size n (n = 1 included; n = 0 is vacuous); reason: footnote 8 (p.8) puts SCFs on profiles with any number of voters and the proof of Lemma 6.2 uses one-voter profiles; the n ≥ 2 reading is false for m ≥ 4 (top choice on one-voter profiles, Borda on {c₁, c₂, c₃} otherwise, has K = 1)
--   - reading: onto: each c wins at some profile → each c wins at some nonempty profile; reason: a profile has voters N = [n]; with the empty list allowed the statement is false (f([]) = c_m, three-candidate Borda elsewhere)
--   - generalization: m ≥ 3 (Section 2) → every m; reason: for m ≤ 2 the conclusion m ≤ K + 2 holds trivially, so the statement specializes to the source
--   - encoding: K ≥ m − 2 → m ≤ K + 2; reason: equivalent; avoids truncated subtraction in ℕ
--   - encoding: profiles ≻_N ∈ L(C)^n, rankings as relations, MP ∈ ℤ_{≥0} ∪ {∞} → List (Ranking m) with rankings as permutations to positions, MP in ℕ∞; reason: Lean convention; same instances
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Theorem 6.1, p.25

import Mathlib
import Definitions.Def_ManipPotential_Anonymous
import Definitions.Def_ManipPotential_Onto
import Definitions.Def_ManipPotential_manipPotentialAt

namespace ManipPotential

/-- Theorem 6.1 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Theorem 6.1, p.25): let `f` be an anonymous and onto social choice
function. If there is an integer `K ≥ 0`, possibly depending on `m` but independent of `n`, such that
`MP(f) ≤ K` uniformly over all electorate sizes, then `K ≥ m − 2`.

**Formalization Note** The bound is required at every electorate size `n` (n = 0 is vacuous);
`m ≤ K + 2` is `K ≥ m − 2` without truncated subtraction, and holds trivially for `m ≤ 2`. -/
theorem theorem_6_1 {m : ℕ} (f : List (Ranking m) → Fin m) (hA : Anonymous f) (hO : Onto f)
    (K : ℕ) (hK : ∀ n : ℕ, manipPotentialAt f n ≤ K) : m ≤ K + 2 := by sorry

end ManipPotential
