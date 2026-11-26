-- Prove2me | Theorems.Thm_LefebvreVariations_waring_seven_cubes_455_to_20000
-- name    : LefebvreVariations.waring_seven_cubes_455_to_20000
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:05:17.45616+00:00
-- url     : https://prove2.me/theorems/75395819-8320-5cb8-8475-128129e7a5ee
-- title:
--   Lefebvre's variations, No. 79 — on a theme by Waring: every integer from 455 to 20000 is a sum of at most seven cubes
-- statement:
--   Every integer $n$ with $455\le n\le 20000$ is a sum of at most $7$ cubes of non-negative integers: there are $s\le 7$ and $a_1,\dots,a_s\in\mathbb{N}$ with $n=a_1^3+\dots+a_s^3$.
--
--   For $G(3)$ the conjecture is that every sufficiently large integer is a sum of at most $4$ cubes; it is known that $G(3)\le 7$ (Linnik, 1943), and the largest integer known to need $7$ cubes is $8042$. The number $454$ is the largest integer that needs $8$ or $9$ cubes, so the bound $455$ is sharp.
--
--   **Formalization Note** The shape `∃ (s : ℕ) (_ : s ≤ 7) (a : Fin s → ℕ), n = ∑ i, (a i) ^ 3` is copied from the parent `waring_g_problem` with $k=3$ and $G=7$; the hypotheses `455 ≤ n ≤ 20000` bound the range. The empty sum covers $n=0$ but $n\ge 455$ here.
--
--   **Why this is a variation.** This is a variation of the open platform problem waring_g_problem (the exact value of G(k) in Waring's problem). It is the case k = 3 played with the explicit bound of seven cubes on the explicit finite range 455 <= n <= 20000, in the parent's own formulation. It is a partial result: the computational base of the known bound G(3) <= 7, and a template for finite checks toward the true value of G(3).
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Linnik, On the representation of large numbers as sums of seven cubes, Mat. Sb. 12 (1943), 218-224 (cited from memory, not re-checked). The facts that 23 and 239 need 9 cubes (Wieferich 1909, Kempner 1912), that 454 is the largest integer needing 8 or more cubes and that 8042 is the largest known needing 7 are cited from memory (Deshouillers, Hennecart and Landreau, 2000, for the computations). The range 455 <= n <= 20000 was checked directly in Python by dynamic programming. The statement uses the shape of the platform theorem waring_g_problem with k = 3.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem waring_seven_cubes_455_to_20000 :
    ∀ n : ℕ, 455 ≤ n → n ≤ 20000 →
      ∃ (s : ℕ) (_ : s ≤ 7) (a : Fin s → ℕ), n = ∑ i, (a i) ^ 3 := by sorry
end LefebvreVariations
