-- Prove2me | Theorems.Thm_LefebvreVariations_waring_nine_cubes
-- name    : LefebvreVariations.waring_nine_cubes
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:04:30.821772+00:00
-- url     : https://prove2.me/theorems/6fd8780f-82e6-4ccd-8491-6e6f84d60546
-- title:
--   Lefebvre's variations: Waring's problem for cubes, g(3) = 9
-- statement:
--   Every natural number is a sum of at most $9$ perfect cubes, and $8$ do not suffice:
--   $$
--   g(3)=9.
--   $$
--   Precisely, every $n\in\mathbb{N}$ can be written as $n=a_1^3+\dots+a_s^3$ with $s\le 9$, $a_i\in\mathbb{N}$, while some $n$ (for instance $n=23$) cannot be written with $s\le 8$.
--
--   **Formalization Note** The statement follows the shape of the platform's `waring_g_problem`: a sum of `s` powers is `n = ∑ i : Fin s, (a i) ^ 3` with `s ≤ 9` and `a : Fin s → ℕ` (zeros are allowed, `s = 0` gives `n = 0`). The second conjunct says there is some `n` that is not such a sum with `s ≤ 8`.
--
--   **Why this is a variation.** A variation on the platform's open `waring_g_problem` (the minimal number g(k) of k-th powers). It fixes k = 3 and states the exact classical value. The parent for every k remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   g(3)=9: A. Wieferich (1909), gap filled by A. J. Kempner (1912) (verified by web search); 23 needs 9 cubes. Parent: Waring's problem, the platform's `waring_g_problem` (open). Verified by web search: Waring's problem article (Wikipedia, MacTutor, Encyclopedia of Mathematics). The minimal number of terms needed was also checked by a dynamic-programming computation for all n up to 20000.

import Mathlib

namespace LefebvreVariations

/-- Waring's problem, `g(3) = 9`: every natural number is a sum of at most 9 `3`-th powers, and 8 do not suffice. Source: A. Wieferich 1909 and A. J. Kempner 1912 (g(3)=9; the integers 23 and 239 need 9 cubes) (cited from memory). -/
theorem waring_nine_cubes :
    (∀ n : ℕ, ∃ (s : ℕ) (_ : s ≤ 9) (a : Fin s → ℕ), n = ∑ i, (a i) ^ 3) ∧
    ¬ (∀ n : ℕ, ∃ (s : ℕ) (_ : s ≤ 8) (a : Fin s → ℕ), n = ∑ i, (a i) ^ 3) := by
  sorry

end LefebvreVariations
