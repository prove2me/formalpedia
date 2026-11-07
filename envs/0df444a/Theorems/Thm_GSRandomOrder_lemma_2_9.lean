-- Prove2me | Theorems.Thm_GSRandomOrder_lemma_2_9
-- name    : GSRandomOrder.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:57.223329+00:00
-- url     : https://prove2.me/theorems/407fa5e0-05e1-43e4-bc5a-62206335c667
-- title:
--   Lemma 2.9 — contraction commutes with the canonical demand
-- statement:
--   Let $v$ be a GS valuation, $S\subseteq N$ and $x\notin S$ with $x\in D_v(S+x)$. Then
--
--   1. $v(\{x\})>-\infty$;
--   2. the contraction $v/x$ of (4) is a GS valuation;
--   3. with labels inherited from $N$,
--   $$
--   D_{v/x}(T)=D_v(T+x)-x\qquad\text{for every }T\subseteq S. \tag{8}
--   $$
--
--   This lets the algorithm reason as if an accepted item had been present from the start: the other items then evolve under $v/x$.
--
--   **Formalization Note** The contraction is defined on all subsets of `Fin n` (with $x$ a dummy item), and clause 2 asserts the exchange axiom for this extension; restricted to $2^{N-x}$ it is the paper's clause.
--
--   Differences from the source:
--   - encoding: GS valuation (Definition 2.1, equivalently the exchange axiom (3) by the cited Theorem 2.3, p.6), values in ℝ ∪ {−∞} → IsGSValuation v: v ∅ = 0 and the exchange axiom (3), v : Finset (Fin n) → WithBot ℝ; reason: the paper defines a GS valuation as one with the two equivalent properties and all its proofs use (3); ⊥ = −∞
--   - generalization: v/x is a GS valuation on 2^{N−x} → IsGSValuation (contract v x) on all of 2^N, with x a dummy item; reason: restriction to 2^{N−x} preserves the exchange axiom (closure paragraph, p.6), so the Lean clause implies the printed one
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), Lemma 2.9, p.8, eq. (8)

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation
import Definitions.Def_GSRandomOrder_contract
import Definitions.Def_GSRandomOrder_canonicalDemand

set_option autoImplicit false

namespace GSRandomOrder

/-- **Lemma 2.9 (Contraction)** (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in Random
Order*, STOC 2027 submission, manuscript sha256 69787f50…, §2.2, p.8, eq. (8)).
Let `v` be a GS valuation, `S ⊆ N` and `x ∉ S` with `x ∈ D_v(S + x)`. Then `v({x}) > −∞`, the
contraction `v/x` of (4) is a GS valuation, and, with labels inherited from `N`,
`D_{v/x}(T) = D_v(T + x) − x` for every `T ⊆ S` (8).

**Formalization Note.** `contract v x` is defined on every subset of `Fin n` (on a set containing
`x` it ignores `x`, a dummy item), and "`v/x` is a GS valuation" is `IsGSValuation (contract v x)`
on all of `Finset (Fin n)`; restricted to `2^{N − x}` it is the paper's statement, and the dummy
extension preserves the exchange axiom (closure paragraph, p.6). -/
theorem lemma_2_9 {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (hv : IsGSValuation v)
    (S : Finset (Fin n)) (x : Fin n) (hxS : x ∉ S) (hxD : x ∈ canonicalDemand v (insert x S)) :
    v {x} ≠ ⊥ ∧ IsGSValuation (contract v x) ∧
      ∀ T ⊆ S, canonicalDemand (contract v x) T = (canonicalDemand v (insert x T)).erase x := by sorry

end GSRandomOrder
