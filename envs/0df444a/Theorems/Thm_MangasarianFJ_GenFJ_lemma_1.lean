-- Prove2me | Theorems.Thm_MangasarianFJ_GenFJ_lemma_1
-- name    : MangasarianFJ.GenFJ.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:26:05.949935+00:00
-- url     : https://prove2.me/theorems/fc5c8a2d-abce-4d9d-bec1-f87f9dab2097
-- title:
--   LEMMA 1, pp. 39–40 — if (2.1) is solvable at x̄ ∈ D, (2.2) is not, and the ∇h_j(x̄) are independent, then (2.3)–(2.4) has no solution
-- statement:
--   Let $D\subseteq E^n$ be open, let $L=\{1,\dots,l\}$ be nonempty ($l\ge1$) and $K=\{1,\dots,k\}$, and let $f_i$ ($i\in L$) and $h_j$ ($j\in K$) be real functions with continuous first partial derivatives on $D$. Suppose that
--
--   1. the system (2.1) $f_i(x)=0$, $i\in L$, $h_j(x)=0$, $j\in K$, has a solution $\bar x\in D$;
--   2. the system (2.2) $f_i(x)<0$, $i\in L$, $h_j(x)=0$, $j\in K$, has no solution in $D$;
--   3. (2.5) the gradients $\nabla h_j(\bar x)$, $j\in K$, are linearly independent.
--
--   Then there is no $y\in E^n$ with
--
--   $$
--   y'\nabla f_i(\bar x)<0,\quad i\in L, \qquad\qquad y'\nabla h_j(\bar x)=0,\quad j\in K. \tag{2.3–2.4}
--   $$
--
--   In words: if no point of $D$ strictly decreases all the $f_i$ while keeping the equalities, then no direction does so to first order, provided the equality gradients are independent. The case $K=\emptyset$ is allowed.
--
--   **Formalization Note** "Continuous first partial derivatives on $D$" is `ContDiffOn ℝ 1 · D`, which in finite dimension is equivalent. Indices are `Fin l`, `Fin k` (0-based). $y'\nabla f$ is the inner product `inner ℝ y (gradient f xbar)`. These $f_i$, $h_j$, $D$ are the lemma's own data, not the problem (1.1).
-- source:
--   Mangasarian and Fromovitz, The Fritz John necessary optimality conditions in the presence of equality and inequality constraints, J. Math. Anal. Appl. 17 (1967), pp. 39–40, LEMMA 1, (2.1)–(2.5); proof in the Appendix, pp. 45–47

import Mathlib

namespace MangasarianFJ.GenFJ
theorem lemma_1 {n l k : ℕ} (hl : 0 < l)
    (f : Fin l → EuclideanSpace ℝ (Fin n) → ℝ) (h : Fin k → EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : IsOpen D)
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) D) (hh : ∀ j, ContDiffOn ℝ 1 (h j) D)
    (xbar : EuclideanSpace ℝ (Fin n)) (hxD : xbar ∈ D)
    (h21 : (∀ i, f i xbar = 0) ∧ ∀ j, h j xbar = 0)
    (h22 : ¬ ∃ x ∈ D, (∀ i, f i x < 0) ∧ ∀ j, h j x = 0)
    (h25 : LinearIndependent ℝ (fun j => gradient (h j) xbar)) :
    ¬ ∃ y : EuclideanSpace ℝ (Fin n),
      (∀ i, inner ℝ y (gradient (f i) xbar) < 0) ∧ ∀ j, inner ℝ y (gradient (h j) xbar) = 0 := by sorry
end MangasarianFJ.GenFJ
