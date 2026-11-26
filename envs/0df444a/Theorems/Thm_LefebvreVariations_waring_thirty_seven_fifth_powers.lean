-- Prove2me | Theorems.Thm_LefebvreVariations_waring_thirty_seven_fifth_powers
-- name    : LefebvreVariations.waring_thirty_seven_fifth_powers
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:05:22.973287+00:00
-- url     : https://prove2.me/theorems/81dfa64d-98de-44d3-8a82-ffd8b93f713f
-- title:
--   Lefebvre's variations: Waring's problem for fifth powers, g(5) = 37
-- statement:
--   Every natural number is a sum of at most $37$ perfect fifth powers, and $36$ do not suffice:
--   $$
--   g(5)=37.
--   $$
--   Precisely, every $n\in\mathbb{N}$ can be written as $n=a_1^5+\dots+a_s^5$ with $s\le 37$, $a_i\in\mathbb{N}$, while some $n$ (for instance $n=223$) cannot be written with $s\le 36$.
--
--   **Formalization Note** The statement follows the shape of the platform's `waring_g_problem`: a sum of `s` powers is `n = ∑ i : Fin s, (a i) ^ 5` with `s ≤ 37` and `a : Fin s → ℕ` (zeros are allowed, `s = 0` gives `n = 0`). The second conjunct says there is some `n` that is not such a sum with `s ≤ 36`.
--
--   **Why this is a variation.** A variation on the platform's open `waring_g_problem` (the minimal number g(k) of k-th powers). It fixes k = 5 and states the exact classical value. The parent for every k remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   g(5)=37: Chen Jingrun (1964) (verified by web search; Wikipedia also credits J. H. Conway independently); 223 needs 37 fifth powers. Parent: Waring's problem, the platform's `waring_g_problem` (open). Verified by web search: Waring's problem article (Wikipedia, MacTutor, Encyclopedia of Mathematics). The minimal number of terms needed was also checked by a dynamic-programming computation for all n up to 20000.

import Mathlib

namespace LefebvreVariations

/-- Waring's problem, `g(5) = 37`: every natural number is a sum of at most 37 `5`-th powers, and 36 do not suffice. Source: J. R. Chen, On Waring's problem for n-th powers, Acta Math. Sinica 8 (1958) / Chen 1964 (g(5)=37; the integer 223 needs 37 fifth powers) (cited from memory). -/
theorem waring_thirty_seven_fifth_powers :
    (∀ n : ℕ, ∃ (s : ℕ) (_ : s ≤ 37) (a : Fin s → ℕ), n = ∑ i, (a i) ^ 5) ∧
    ¬ (∀ n : ℕ, ∃ (s : ℕ) (_ : s ≤ 36) (a : Fin s → ℕ), n = ∑ i, (a i) ^ 5) := by
  sorry

end LefebvreVariations
