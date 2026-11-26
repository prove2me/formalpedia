-- Prove2me | Theorems.Thm_LefebvreVariations_waring_nineteen_fourth_powers
-- name    : LefebvreVariations.waring_nineteen_fourth_powers
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:04:58.162259+00:00
-- url     : https://prove2.me/theorems/c19152b1-2062-5b67-96e7-6baa5744dd5f
-- title:
--   Lefebvre's variations, No. 120 — on a theme by Edward Waring and David Hilbert: Waring's problem for fourth powers, g(4) = 19
-- statement:
--   Every natural number is a sum of at most $19$ perfect fourth powers, and $18$ do not suffice:
--   $$
--   g(4)=19.
--   $$
--   Precisely, every $n\in\mathbb{N}$ can be written as $n=a_1^4+\dots+a_s^4$ with $s\le 19$, $a_i\in\mathbb{N}$, while some $n$ (for instance $n=79$) cannot be written with $s\le 18$.
--
--   **Formalization Note** The statement follows the shape of the platform's `waring_g_problem`: a sum of `s` powers is `n = ∑ i : Fin s, (a i) ^ 4` with `s ≤ 19` and `a : Fin s → ℕ` (zeros are allowed, `s = 0` gives `n = 0`). The second conjunct says there is some `n` that is not such a sum with `s ≤ 18`.
--
--   **Why this is a variation.** A variation on the platform's open `waring_g_problem` (the minimal number g(k) of k-th powers). It fixes k = 4 and states the exact classical value. The parent for every k remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   g(4)=19: R. Balasubramanian, J.-M. Deshouillers and F. Dress (1986, two papers) (verified by web search); 79 needs 19 fourth powers. Parent: Waring's problem, the platform's `waring_g_problem` (open). Verified by web search: Waring's problem article (Wikipedia, MacTutor, Encyclopedia of Mathematics). The minimal number of terms needed was also checked by a dynamic-programming computation for all n up to 20000.

import Mathlib

namespace LefebvreVariations

/-- Waring's problem, `g(4) = 19`: every natural number is a sum of at most 19 `4`-th powers, and 18 do not suffice. Source: R. Balasubramanian, J.-M. Deshouillers and F. Dress, Probleme de Waring pour les bicarres, C. R. Acad. Sci. Paris 303 (1986) (g(4)=19; the integer 79 needs 19 fourth powers) (cited from memory). -/
theorem waring_nineteen_fourth_powers :
    (∀ n : ℕ, ∃ (s : ℕ) (_ : s ≤ 19) (a : Fin s → ℕ), n = ∑ i, (a i) ^ 4) ∧
    ¬ (∀ n : ℕ, ∃ (s : ℕ) (_ : s ≤ 18) (a : Fin s → ℕ), n = ∑ i, (a i) ^ 4) := by
  sorry

end LefebvreVariations
