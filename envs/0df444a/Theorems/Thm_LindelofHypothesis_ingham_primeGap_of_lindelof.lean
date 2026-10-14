-- Prove2me | Theorems.Thm_LindelofHypothesis_ingham_primeGap_of_lindelof
-- name    : LindelofHypothesis.ingham_primeGap_of_lindelof
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:50:55.412729+00:00
-- url     : https://prove2.me/theorems/ac3b5726-e8ef-4ab5-a72e-a272a69936a5
-- title:
--   Ingham: under Lindelöf, $g_n\ll p_n^{1/2+\varepsilon}$
-- statement:
--   Let $p_n$ be the $n$-th prime and $g_n=p_{n+1}-p_n$. Assume the Lindelöf hypothesis. Then for every $\varepsilon>0$,
--   $$g_n\ll p_n^{1/2+\varepsilon}$$
--   for all sufficiently large $n$, i.e. $g_n=O(p_n^{1/2+\varepsilon})$ as $n\to\infty$.
--
--   This is Ingham's consequence of the Lindelöf hypothesis for gaps between consecutive primes.
--
--   **Formalization Note** `RiemannVonMangoldt.LindelofHypothesis` is the published definition: for every $\varepsilon>0$, $\zeta(\tfrac12+it)=O(t^{\varepsilon})$ as $t\to+\infty$. Primes are indexed from $0$ ($p_0=2$), which does not affect the asymptotic statement.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; section "Other consequences", first displayed formula (result of Albert Ingham).

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem ingham_primeGap_of_lindelof (hL : RiemannVonMangoldt.LindelofHypothesis)
    (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (primeGap n : ℝ)) =O[atTop] (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) ^ (1 / 2 + ε)) := by sorry

end LindelofHypothesis
