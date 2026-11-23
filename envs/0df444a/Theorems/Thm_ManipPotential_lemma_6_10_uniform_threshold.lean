-- Prove2me | Theorems.Thm_ManipPotential_lemma_6_10_uniform_threshold
-- name    : ManipPotential.lemma_6_10_uniform_threshold
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:35:29.215091+00:00
-- url     : https://prove2.me/theorems/a8e483e5-34de-4828-9604-dbdc604bacff
-- title:
--   Lemma 6.10 — uniform cyclic threshold at a perturbed common junction
-- statement:
--   Let $m\ge 3$, let $g$ satisfy the three axioms of Lemma 6.2 with $\lambda=K+1$, and let $P$ be a common junction. Suppose $0<\varepsilon<\tfrac12\min_r P_r$, and let $Z$ be a rational profile with strictly positive coordinates satisfying
--
--   $$
--   \|Z-(P-\varepsilon\mathbf 1)\|_\infty<\frac{\varepsilon}{4}.
--   $$
--
--   Then there is a rational $u_0\ge 0$ such that
--
--   $$
--   u_0<2\lambda\,m!\,\varepsilon
--   $$
--
--   and, for every candidate index $j$ and every rational $u>u_0$,
--
--   $$
--   g(Z+u\ell_j)=c_j.
--   $$
--
--   This is the uniform threshold constructed in the first part of the proof of Lemma 6.10. For each $j$, one approximates $P$ by a rational profile electing $c_j$, replaces the surplus over $Z$ using bounded manipulation potential, and then applies conditional participation. The displayed bound allows Lemma 6.3 to be applied with the same background $Z$ for all $j$.
--
--   **Formalization Note** Rational profiles and their cyclic increments are coerced coordinatewise to $\mathbb R$ in the approximation estimate. The norm is the sup norm on functions from rankings to $\mathbb R$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), proof of Lemma 6.10, paragraphs 2–4, p.33 (PDF page 33; printed page 32).

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_IsCommonJunction
import Definitions.Def_ManipPotential_cycL

/-- The uniform cyclic threshold constructed in the first part of the proof of
Lemma 6.10 (Berker–Conitzer–Hartman–Liu–Oesterheld, arXiv:2602.22838, p.33). -/
theorem ManipPotential.lemma_6_10_uniform_threshold {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ)
    (g : (Ranking m → ℚ) → Fin m) (hg : GAxioms K g)
    (P : Ranking m → ℝ) (hP : IsCommonJunction g P) (ε : ℝ) (hε : 0 < ε)
    (hεP : ε < (1 / 2) * Finset.univ.inf' Finset.univ_nonempty P)
    (Z : Ranking m → ℚ) (hZ : ∀ r, 0 < Z r)
    (hZP : ‖(fun r => (Z r : ℝ)) - (P - (fun _ => ε))‖ < ε / 4) :
    ∃ u₀ : ℚ, 0 ≤ u₀ ∧
      (u₀ : ℝ) < 2 * ((K : ℝ) + 1) * (m.factorial : ℝ) * ε ∧
      ∀ (j : Fin m) (u : ℚ), u₀ < u → g (Z + u • unitVec (ell j)) = j := by sorry
