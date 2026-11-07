-- Prove2me | Theorems.Thm_LocalBreadth_corollary_5_10
-- name    : LocalBreadth.corollary_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:00.575545+00:00
-- url     : https://prove2.me/theorems/f2b654e8-8f07-48c4-9d70-9e9e9ac634e3
-- title:
--   Corollary 5.10 — protected sets
-- statement:
--   Let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z$.
--   Fix $A\in\mathcal X$, $n\ge1$ and $q<b_n(A)$. Then:
--
--   1. the one-language history $(A)$ is $(A,n,q)$-safe;
--   2. every $(A,n,q)$-safe history $H$ satisfies $c_n(H)>q$;
--   3. if an $(A,n,q)$-safe history $H$ ends at $M$, then there is a finite set $\mathrm{Prot}(H)\subseteq M$ such that every $L\in\mathcal X$ with $\mathrm{Prot}(H)\subseteq L\subsetneq M$ makes $H^\frown L$ $(A,n,q)$-safe.
--
--   These are the local certificates from which the generator's forest is assembled.
--
--   Differences from the source:
--   - encoding: histories as chains $H$ with parameters $(A,n,q)$ → safety on the chain list, with $A$ its first language; reason: $c_n$ reads $A$ from the chain; same notion
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Corollary 5.10, pp.29–30

import Mathlib
import Definitions.Def_LocalBreadth_History
import Definitions.Def_LocalBreadth_bComb
import Definitions.Def_LocalBreadth_IsSafe

namespace LocalBreadth

/-- Corollary 5.10 (Protected sets). Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…),
pp.29–30. Fix `A ∈ X`, `n ≥ 1`, `q < b_n(A)`. Then (1) the one-language history `(A)` is safe; (2) every
safe history starting at `A` has `c_n(H) > q`; (3) a safe history ending at `M` has a finite `Prot(H) ⊆ M`
such that every `L ∈ X` with `Prot(H) ⊆ L ⊊ M` makes `H⌢L` safe. -/
theorem corollary_5_10 (X : Set (Set ℤ)) (hne : X.Nonempty) (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite)
    (A : Set ℤ) (hA : A ∈ X) (n : ℕ) (hn : 1 ≤ n) (q : ℝ) (hq : q < bComb X n A) :
    IsSafe X n q [A] ∧
    (∀ H : History X, H.first = A → IsSafe X n q H.chain → q < cScore n H.chain) ∧
    (∀ H : History X, H.first = A → IsSafe X n q H.chain →
      ∃ F : Finset ℤ, IsProtectedSet X n q H.chain F) := by sorry

end LocalBreadth
