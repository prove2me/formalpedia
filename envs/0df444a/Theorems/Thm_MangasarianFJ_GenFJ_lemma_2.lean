-- Prove2me | Theorems.Thm_MangasarianFJ_GenFJ_lemma_2
-- name    : MangasarianFJ.GenFJ.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:25:54.592431+00:00
-- url     : https://prove2.me/theorems/188ed21f-7ef9-4043-adb3-1628a3ab0f72
-- title:
--   LEMMA 2, p. 40 — under Lemma 1's assumptions there are r̄ ≥ 0, s̄ with Σ r̄_i∇f_i(x̄) + Σ s̄_j∇h_j(x̄) = 0 and (r̄, s̄) ≠ 0
-- statement:
--   Let $D\subseteq E^n$ be open, $L=\{1,\dots,l\}$ nonempty, $K=\{1,\dots,k\}$, and let $f_i$ ($i\in L$), $h_j$ ($j\in K$) have continuous first partial derivatives on $D$. Suppose the system $f_i(x)=0$ ($i\in L$), $h_j(x)=0$ ($j\in K$) has a solution $\bar x\in D$ and the system $f_i(x)<0$ ($i\in L$), $h_j(x)=0$ ($j\in K$) has no solution in $D$. Then there exist $\bar r\in E^l$, $\bar s\in E^k$ with
--
--   $$
--   \sum_{i=1}^l\bar r_i\nabla f_i(\bar x)+\sum_{j=1}^k\bar s_j\nabla h_j(\bar x)=0, \tag{2.6}
--   $$
--
--   $$
--   \bar r\ge 0, \tag{2.7}
--   $$
--
--   $$
--   (\bar r,\bar s)\ne 0. \tag{2.8}
--   $$
--
--   No linear independence of the $\nabla h_j(\bar x)$ is assumed: Lemma 2 is the multiplier form of Lemma 1 valid in general, and it is the step from which the generalized Fritz John conditions follow.
--
--   **Formalization Note** "The assumptions of Lemma 1" are taken without the proviso (2.5) (linear independence of the $\nabla h_j(\bar x)$), which on the page qualifies Lemma 1's conclusion; the paper's proof of Lemma 2 treats the linearly dependent case separately, and the main theorem applies Lemma 2 with no independence hypothesis. $(\bar r,\bar s)\ne0$ is `r ≠ 0 ∨ s ≠ 0`. Indices are `Fin l`, `Fin k` (0-based).
-- source:
--   Mangasarian and Fromovitz, The Fritz John necessary optimality conditions in the presence of equality and inequality constraints, J. Math. Anal. Appl. 17 (1967), p. 40, LEMMA 2, (2.6)–(2.8)

import Mathlib

namespace MangasarianFJ.GenFJ
theorem lemma_2 {n l k : ℕ} (hl : 0 < l)
    (f : Fin l → EuclideanSpace ℝ (Fin n) → ℝ) (h : Fin k → EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : IsOpen D)
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) D) (hh : ∀ j, ContDiffOn ℝ 1 (h j) D)
    (xbar : EuclideanSpace ℝ (Fin n)) (hxD : xbar ∈ D)
    (h21 : (∀ i, f i xbar = 0) ∧ ∀ j, h j xbar = 0)
    (h22 : ¬ ∃ x ∈ D, (∀ i, f i x < 0) ∧ ∀ j, h j x = 0) :
    ∃ (r : Fin l → ℝ) (s : Fin k → ℝ),
      ∑ i, r i • gradient (f i) xbar + ∑ j, s j • gradient (h j) xbar = 0 ∧
      (∀ i, 0 ≤ r i) ∧ (r ≠ 0 ∨ s ≠ 0) := by sorry
end MangasarianFJ.GenFJ
