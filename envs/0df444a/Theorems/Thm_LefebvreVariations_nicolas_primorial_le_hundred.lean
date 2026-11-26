-- Prove2me | Theorems.Thm_LefebvreVariations_nicolas_primorial_le_hundred
-- name    : LefebvreVariations.nicolas_primorial_le_hundred
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:19:46.673192+00:00
-- url     : https://prove2.me/theorems/819f630d-4c0d-449b-8e64-cc1d9c468e89
-- title:
--   Lefebvre's variations, No. 153 — on a theme by Nicolas: Nicolas' primorial inequality holds for all primes up to one hundred
-- statement:
--   For every prime $p\le100$, with $n=p\#=\prod_{q\le p}q$ the primorial,
--   $$
--   \frac{n}{\varphi(n)}\ >\ e^{\gamma}\,\log\log n ,
--   $$
--   where $\gamma$ is Euler's constant. For $p=2$ the right side is negative.
--
--   The parent asserts this for all primes $p$, which by Nicolas' theorem is equivalent to the Riemann hypothesis. At $p=97$ the two sides are $8.3114\ldots$ and $7.8858\ldots$.
--
--   **Formalization Note** The statement is that of `BroughanRH.nicolasPrimorial` verbatim (`primorial p`, `Nat.totient`, `Real.eulerMascheroniConstant`), with the added hypothesis `p ≤ 100`.
--
--   **Why this is a variation.** Variation on the open platform theorem BroughanRH.nicolasPrimorial (Nicolas' criterion, equivalent to the Riemann hypothesis): the parent's own inequality for the 25 primorials p# with p <= 100, a finite list of explicit integers.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   J.-L. Nicolas, Petites valeurs de la fonction d'Euler, J. Number Theory 17 (1983), 375-388 (title, journal, volume and pages confirmed by web search). Statement as on the platform (BroughanRH.nicolasPrimorial). Truth check: computed in Python (mpmath, 40 digits) for every prime p < 2000: no violation; for example p = 3: 3.0 vs 1.0387; p = 13: 5.2135 vs 4.1554; p = 97: 8.3114 vs 7.8858; p = 199: 9.6251 vs 9.3318.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

theorem nicolas_primorial_le_hundred :
    ∀ p : ℕ, p.Prime → p ≤ 100 →
      let n := primorial p
      (n : ℝ) / n.totient > Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) := by
  sorry

end LefebvreVariations
