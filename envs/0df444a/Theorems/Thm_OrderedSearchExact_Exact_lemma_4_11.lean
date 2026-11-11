-- Prove2me | Theorems.Thm_OrderedSearchExact_Exact_lemma_4_11
-- name    : OrderedSearchExact.Exact.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:13.005925+00:00
-- url     : https://prove2.me/theorems/ed724974-9bc2-4160-a5b1-44cf481366a5
-- title:
--   Lemma 4.11 — two-query exactifier for either parity
-- statement:
--   Let $n\ge1$ and let a feasible $k$-step Laurent prefix end at $R(z)=1+\sum_{j=1}^{n-1}a_j(z^j+z^{-j})$. If
--
--   $$2\sum_{j=1}^{n-1}|a_j|<1,$$
--
--   then the concrete two-step exactifier extends this prefix to a feasible $(k+2)$-step path ending exactly at $1$. Every original step is retained. At the next query it erases the component allowed by that query's parity, and at the following query it erases the remaining component. This handles either next parity and includes the singleton list.
--
--   Differences from the source:
--   - encoding: normalized real symmetric Laurent polynomials of degree less than n → real coefficient vectors indexed by Fin (n-1), with frequency i+1 and evaluation on every real angle; reason: this bijects the source coefficients, preserves the constant coefficient 1, and includes all points of the unit circle
--   - encoding: two additional queries terminate the feasible path at 1 → the defined exactify operation has a feasible path of length k+2 and agrees with the original prefix through k; reason: these are the concrete two operations in the proof; no optimal stopping time or abstract completion oracle is substituted
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), Lemma 4.11, p.22 (PDF p.22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Laurent

namespace OrderedSearchExact.Exact

theorem lemma_4_11 (n k : ℕ) (hn : 1 ≤ n) (p : ℕ → Coeff n)
    (hp : FeasiblePrefix n k p) (hm : mass (p k) < 1) :
    FeasiblePath n (k + 2) (exactify p k) ∧
      (∀ t, t ≤ k → exactify p k t = p t) := by sorry

end OrderedSearchExact.Exact
