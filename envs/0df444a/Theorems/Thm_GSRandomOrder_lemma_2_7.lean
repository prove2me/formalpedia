-- Prove2me | Theorems.Thm_GSRandomOrder_lemma_2_7
-- name    : GSRandomOrder.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:58.057621+00:00
-- url     : https://prove2.me/theorems/af62fb8d-dc04-40b8-9d82-0e97629e560c
-- title:
--   Lemma 2.7 — single exchange, persistence and single displacement
-- statement:
--   Let $v$ be a GS valuation, $T\subseteq N$, $x\notin T$ and $X=D_v(T)$. Then
--   $$
--   D_v(T+x)\in\{X,\ X+x\}\cup\{X+x-f: f\in X\}. \tag{5}
--   $$
--   Consequently the canonical demand has the two properties
--   $$
--   \text{persistence: } T\subseteq U\implies D_v(U)\cap T\subseteq D_v(T), \tag{6}
--   $$
--   $$
--   \text{single displacement: } x\notin T\implies |D_v(T)\setminus D_v(T+x)|\le 1. \tag{7}
--   $$
--
--   Adding one item changes the canonical demand by at most one exchange; an item rejected from a set is rejected from every larger set. These are the only facts about $D_v$ that the comparison inequality uses.
--
--   Differences from the source:
--   - encoding: GS valuation (Definition 2.1, equivalently the exchange axiom (3) by the cited Theorem 2.3, p.6), values in ℝ ∪ {−∞} → IsGSValuation v: v ∅ = 0 and the exchange axiom (3), v : Finset (Fin n) → WithBot ℝ; reason: the paper defines a GS valuation as one with the two equivalent properties and all its proofs use (3); ⊥ = −∞
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), Lemma 2.7, p.7, eqs. (5)–(7)

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation
import Definitions.Def_GSRandomOrder_canonicalDemand

set_option autoImplicit false

namespace GSRandomOrder

/-- **Lemma 2.7 (Single exchange)** (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in Random
Order*, STOC 2027 submission, manuscript sha256 69787f50…, §2.2, p.7, eqs. (5)–(7)).
Let `v` be a GS valuation, `T ⊆ N`, `x ∉ T` and `X = D(T)`. Then
`D(T + x) ∈ {X, X + x} ∪ {X + x − f : f ∈ X}` (5). Consequently `D` has the two properties
persistence, `T ⊆ U ⟹ D(U) ∩ T ⊆ D(T)` (6), and single displacement,
`x ∉ T ⟹ |D(T) \ D(T + x)| ≤ 1` (7).

**Formalization Note.** `D = canonicalDemand v`; the three displays are the three conjuncts,
each quantified over all `T`, `U`, `x` as in the lemma. -/
theorem lemma_2_7 {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (hv : IsGSValuation v) :
    (∀ (T : Finset (Fin n)) (x : Fin n), x ∉ T →
      canonicalDemand v (insert x T) = canonicalDemand v T ∨
        canonicalDemand v (insert x T) = insert x (canonicalDemand v T) ∨
        ∃ f ∈ canonicalDemand v T,
          canonicalDemand v (insert x T) = (insert x (canonicalDemand v T)).erase f) ∧
    (∀ T U : Finset (Fin n), T ⊆ U → canonicalDemand v U ∩ T ⊆ canonicalDemand v T) ∧
    (∀ (T : Finset (Fin n)) (x : Fin n), x ∉ T →
      (canonicalDemand v T \ canonicalDemand v (insert x T)).card ≤ 1) := by sorry

end GSRandomOrder
