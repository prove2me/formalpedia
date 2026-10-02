-- Prove2me | Theorems.Thm_OPG37364_exists_lps13_prime_above
-- name    : OPG37364.exists_lps13_prime_above
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T13:27:09.270413+00:00
-- url     : https://prove2.me/theorems/00135dd9-7873-4088-9ad5-bf1621df5ae6
-- title:
--   Arbitrarily large primes for the fixed-p=13 LPS arithmetic setup
-- statement:
--   For every natural number $B$, there is a prime $q$ such that
--
--   $$q>\max\{B,13\},\qquad q\equiv5\pmod{52},\qquad q\equiv1\pmod4,\qquad \left(\frac{13}{q}\right)=-1.$$
--
--   All properties hold for the same prime. Thus suitable primes can be selected above any later size threshold; no effective bound or particular prime is prescribed.
--
--   This is the fixed-$p=13$ arithmetic step in the Feghali–Lucke–Paulusma–Ries/Lubotzky–Phillips–Sarnak route. Dirichlet's theorem supplies primes in the progression $5+52k$. Reduction modulo $13$ gives $(q/13)=(5/13)=-1$, and quadratic reciprocity gives $(13/q)=-1$. The conclusion is only arithmetic and makes no graph-construction claim.
--
--   Formalization note: Mathlib writes the symbol as `legendreSym q 13`. The existential prime-proof binder supplies the required `Fact q.Prime` instance; it does not introduce an additional mathematical assumption.
-- source:
--   Feghali, Lucke, Paulusma and Ries, Matching Cuts in Graphs of High Girth and H-Free Graphs, Algorithmica 87 (2025), Lemma 4 and the arithmetic hypotheses in Lemma 5, https://link.springer.com/article/10.1007/s00453-025-01318-8 . Lemma 4 states (q/13)=-1; this formalization explicitly applies quadratic reciprocity to obtain (13/q)=-1. LPS: Lubotzky, Phillips and Sarnak, Ramanujan graphs, Combinatorica 8 (1988), p. 262, https://doi.org/10.1007/BF02126799 . Classical Dirichlet/reciprocity specialization, not new mathematics.

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.NormNum.LegendreSymbol
set_option autoImplicit false

namespace OPG37364

theorem exists_lps13_prime_above (B : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime),
      max B 13 < q ∧ q ≡ 5 [MOD 52] ∧ q ≡ 1 [MOD 4] ∧
      @legendreSym q ⟨hq⟩ 13 = -1 := by sorry

end OPG37364
