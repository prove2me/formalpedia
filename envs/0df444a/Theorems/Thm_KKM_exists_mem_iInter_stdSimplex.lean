-- Prove2me | Theorems.Thm_KKM_exists_mem_iInter_stdSimplex
-- name    : KKM.exists_mem_iInter_stdSimplex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T04:08:05.072446+00:00
-- url     : https://prove2.me/theorems/55792f73-83f2-4930-9c6f-cca047b157d9
-- title:
--   The KKM covering lemma on the standard simplex
-- statement:
--   Let $\Delta^n = \{x \in \mathbb{R}^{n+1} : x_i \ge 0,\ \sum_i x_i = 1\}$ be the standard
--   $n$-simplex, with vertices $e_0, \dots, e_n$ (the indicator vectors). Let $A_0, \dots, A_n$ be
--   open sets with
--
--   1. $\Delta^n \subseteq \bigcup_i A_i$ — they cover the simplex;
--   2. $\Delta^n \setminus A_i$ is convex for every $i$;
--   3. $e_i \notin A_j$ whenever $i \ne j$ — each vertex is missed by every set but its own.
--
--   Then the sets have a common point inside the simplex:
--
--   $$
--   \exists\, x \in \Delta^n \ \text{ such that } \ x \in A_i \ \text{ for every } i .
--   $$
--
--   This is the covering form of the Knaster–Kuratowski–Mazurkiewicz lemma, in the
--   concrete coordinates of the standard simplex. It is the combinatorial heart of the
--   KKM–Brouwer circle of results: minimax theorems, the existence of Nash equilibria and
--   Sperner-type arguments all reduce to a statement of this shape, and the hypothesis that each
--   complement $\Delta^n \setminus A_i$ is convex is what replaces the labelling condition in the
--   simplicial version.
-- source:
--   B. Knaster, C. Kuratowski and S. Mazurkiewicz, Ein Beweis des Fixpunktsatzes für n-dimensionale Simplexe, Fund. Math. 14 (1929), 132–137; M. Sion, On general minimax theorems, Pacific J. Math. 8 (1958), 171–176, Theorem 3.1 (p. 173). Carved from the accepted proof of SionMinimax.KKM.lemma_3_3, https://prove2.me/submissions/818ed08f-1f44-45cc-90a9-3239f8bb6e07

import Mathlib

open Fin.NatCast

theorem KKM.exists_mem_iInter_stdSimplex (n : ℕ) (A : Fin (n+1) → Set (Fin (n+1) → ℝ)) (hA : ∀ i, IsOpen (A i))
    (hcov : ∀ x ∈ stdSimplex ℝ (Fin (n+1)), ∃ i, x ∈ A i)
    (hC : ∀ i, Convex ℝ (stdSimplex ℝ (Fin (n+1)) \ A i))
    (hv : ∀ i j, i ≠ j → (Pi.single i 1 : Fin (n+1) → ℝ) ∉ A j) :
    ∃ x ∈ stdSimplex ℝ (Fin (n+1)), ∀ i, x ∈ A i := by sorry
