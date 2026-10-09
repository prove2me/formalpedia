-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_constructions
-- name    : LinearPathTuran.Exact.constructions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:30.102756+00:00
-- url     : https://prove2.me/theorems/5ff8615f-f063-434d-8eb6-7fa5b6286ffe
-- title:
--   pp. 4, 9, 11 — the extremal families are ℙ-free and have f(n,k,t) and g(n,k,t) members
-- statement:
--   Let $k\ge 4$ and $t\ge 1$, and let $n\ge 0$.
--
--   1. If $S\subseteq[n]$ has $|S|=t$, the family $\mathcal F_S$ of all $k$-subsets of $[n]$ meeting $S$ contains no linear path $\mathbb P_{2t+1}^{(k)}$, and $|\mathcal F_S|=f(n,k,t)$.
--   2. If moreover $u,v\in[n]\setminus S$ are distinct, the family $\mathcal F_S\cup\{F\in\binom{[n]\setminus S}{k}: u,v\in F\}$ contains no $\mathbb P_{2t+2}^{(k)}$ and has exactly $g(n,k,t)$ members.
--
--   In formulas,
--   $$|\mathcal F_S|=\sum_{i=1}^t\binom{n-i}{k-1},\qquad \Big|\mathcal F_S\cup\{F: F\cap S=\emptyset,\ u,v\in F\}\Big|=\sum_{i=1}^t\binom{n-i}{k-1}+\binom{n-t-2}{k-2}.$$
--
--   These are the lower-bound halves of Theorem 2.4: the two families attain the claimed values of $\mathbf{ex}_k(n,\mathbb P^{(k)}_{2t+1})$ and $\mathbf{ex}_k(n,\mathbb P^{(k)}_{2t+2})$.
--
--   **Formalization Note** The statement is asserted for every $n$; $|S|=t$ forces $n\ge t$, and $u,v\notin S$ distinct forces $n\ge t+2$, where the natural-number subtractions in $f$ and $g$ are exact.
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 4 ("It is easy to see that the constructions … are indeed ℙ_ℓ^(k) … -free"), p. 9 (§5, f and g count these families), p. 11 (|F_S| = f(n,k,t))

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_Setting

namespace LinearPathTuran.Exact

open Finset

/-- pp. 4, 9, 11: the two extremal families are linear-path-free and have `f(n,k,t)` and
`g(n,k,t)` members. -/
theorem constructions (n k t : ℕ) (hk : 4 ≤ k) (ht : 1 ≤ t) :
    (∀ S : Finset (Fin n), #S = t →
        ¬ ContainsLinearPath (starFamily n k S) (2 * t + 1) ∧
          #(starFamily n k S) = fNum n k t) ∧
    (∀ (S : Finset (Fin n)) (u v : Fin n), #S = t → u ∉ S → v ∉ S → u ≠ v →
        ¬ ContainsLinearPath (evenFamily n k S u v) (2 * t + 2) ∧
          #(evenFamily n k S u v) = gNum n k t) := by sorry

end LinearPathTuran.Exact
