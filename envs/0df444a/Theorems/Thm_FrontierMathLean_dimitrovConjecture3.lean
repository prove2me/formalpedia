-- Prove2me | Theorems.Thm_FrontierMathLean_dimitrovConjecture3
-- name    : FrontierMathLean.dimitrovConjecture3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:55:34.615874+00:00
-- url     : https://prove2.me/theorems/160f0fcd-fc2f-4949-a590-e8087496ec67
-- title:
--   Frontier Math Lean: dimitrov Conjecture3
-- statement:
--   **Dimitrov's Conjecture 3** from arXiv:2606.12484v1, formalized over `ℚ`.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture3.lean#L63-L79
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture3.lean#L63-L79

import Definitions.Def_FrontierMathLean_DimitrovConjecture1
import Definitions.Def_FrontierMathLean_NesbittRatioInequality
import Definitions.Def_FrontierMathLean_DimitrovConjecture3
set_option autoImplicit false
open scoped ArithmeticFunction.sigma
open FrontierMathLean

theorem FrontierMathLean.dimitrovConjecture3 (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (4 * ((n : ℚ) + 1) ^ (2 * k)
          + (((n : ℚ) ^ 2 - 1) ^ k)
          + ((n : ℚ) - 1) ^ (2 * k)) /
        (2 * (((n : ℚ) + 1) ^ (2 * k)
          + (((n : ℚ) ^ 2 - 1) ^ k))) ≤
      (n.totient : ℚ) ^ k /
          ((dedekindPsi n : ℚ) ^ k
            + (ArithmeticFunction.sigma 1 n : ℚ) ^ k) +
        (dedekindPsi n : ℚ) ^ k /
          ((n.totient : ℚ) ^ k
            + (ArithmeticFunction.sigma 1 n : ℚ) ^ k) +
        (ArithmeticFunction.sigma 1 n : ℚ) ^ k /
          ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k) := by sorry
