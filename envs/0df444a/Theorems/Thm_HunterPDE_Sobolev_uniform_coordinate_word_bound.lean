-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_uniform_coordinate_word_bound
-- name    : HunterPDE.Sobolev.uniform_coordinate_word_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T21:40:54.749969+00:00
-- url     : https://prove2.me/theorems/e85ab126-32c8-4ff4-bba1-a4faec73c64a
-- title:
--   Uniform ordered coordinate derivative bounds under scalar contractions
-- statement:
--   Let $f\in C_c^\infty(\mathbb R^n)$ and let $l=(i_1,\ldots,i_m)$ be a finite ordered list of coordinate directions. There exists $C\ge0$, depending on $f$ and $l$, such that for all real numbers $a,b,c$ with $|a|,|b|,|c|\le1$,
--
--   $$\left|\partial_{i_m}\cdots\partial_{i_1}[a+b f(c\,\cdot)](x)\right|\le C\qquad(x\in\mathbb R^n).$$
--
--   The empty list means the function itself. Negative and zero contractions are included, and no support condition on the affine expression is required. The proof uses compact support to bound $f$ at order zero. Each subsequent coordinate derivative replaces $f$ with its smooth compactly supported coordinate derivative, $a$ with zero, and $b$ with $bc$. This gives uniform estimates for arbitrary derivative words, including expanding cutoff jets.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Section 1.8, printed p. 10, and the scaled cutoff argument in the proof of Theorem 3.24, printed p. 59. This is a generalized auxiliary consequence of the chain rule and compact support, not a verbatim numbered theorem.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace

open HunterPDE.Sobolev

theorem HunterPDE.Sobolev.uniform_coordinate_word_bound {n : ℕ} (l : List (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsTestFunction Set.univ f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b c : ℝ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 →
      ∀ x, ‖l.foldl (fun g i => partialDeriv i g) (fun y => a + b * f (c • y)) x‖ ≤ C  := by sorry
