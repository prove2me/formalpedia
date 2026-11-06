-- Prove2me | Theorems.Thm_GradSuffice_proposition_1
-- name    : GradSuffice.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:06.655602+00:00
-- url     : https://prove2.me/theorems/ee426e19-cdf6-4426-9dcf-630f019fa462
-- title:
--   Proposition 1, p.11 — a tree full of love: a fully loving subtree of depth $\ge c\gamma^2 n/\log(e/\gamma)$
-- statement:
--   Let $T$ be the complete binary tree of depth $n$, and suppose that each branch $\beta$ loves some of the $n$ internal vertices it visits.
--
--   **Proposition 1 (a tree full of love).** There is a universal constant $c>0$ such that, for every $0<\gamma\le1/2$: if a uniformly random branch loves at least $(1/2+\gamma)n$ of its internal vertices in expectation, then $T$ contains a fully loving complete binary subtree of depth at least
--   $$c\,\frac{\gamma^2}{\log(e/\gamma)}\,n .$$
--
--   At $\gamma=0$ no such statement holds (p.11): each branch may love exactly the vertices where it takes its majority direction. The proposition is the combinatorial step of Theorem 3, turning average shattering (Lemma 4) into a fully shattered tree.
--
--   Differences from the source:
--   - encoding: subtrees closed under least common ancestors, fully loving → IsFullyLovingSubtree: levels of the retained vertices plus one witnessing branch per subtree branch; reason: equivalent description; terminal vertices are original leaves as App. B allows
--   - encoding: "a uniformly random branch loves at least (1/2 + γ)n … in expectation" → the average over the 2^n branches of the number of loved vertices is ≥ (1/2 + γ)n; reason: uniform expectation over a finite set
--   - reading: log (no base printed) → natural logarithm; reason: the e in log(e/γ) indicates the natural logarithm
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Proposition 1, p.11

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_GradSuffice_IsFullyLovingSubtree

namespace GradSuffice

/-- **Proposition 1 (a tree full of love).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Proposition 1, p.11: "There is a universal constant
`c > 0` such that the following holds. Let `T` be a complete binary tree of depth `n`, and let
`0 < γ ≤ 1/2`. If a uniformly random branch loves at least `(1/2 + γ)n` of its internal vertices in
expectation, then `T` contains a fully loving complete binary subtree of depth at least
`c γ² / log(e/γ) · n`."

**Formalization Note.** Branches of `T` are `β : Fin n → Bool`; `love β l` says that `β` loves its
internal vertex at level `l`. The expectation over a uniformly random branch is the average over the
`2^n` branches of the number of loved vertices. Fully loving complete binary subtrees are encoded by
`IsFullyLovingSubtree`. `log` is natural. -/
theorem proposition_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (love : (Fin n → Bool) → Fin n → Prop) (γ : ℝ), 0 < γ → γ ≤ 1 / 2 →
      (1 / 2 + γ) * n ≤ (2 ^ n : ℝ)⁻¹ * ∑ β : Fin n → Bool, (Nat.card {l : Fin n // love β l} : ℝ) →
      ∃ d : ℕ, c * γ ^ 2 / Real.log (Real.exp 1 / γ) * n ≤ d ∧
        ∃ (lev : NondualOpt.Tree (Fin n) d) (br : (Fin d → Bool) → Fin n → Bool),
          IsFullyLovingSubtree love lev br := by sorry

end GradSuffice
