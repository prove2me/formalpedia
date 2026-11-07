-- Prove2me | Theorems.Thm_GSRandomOrder_proposition_B_6
-- name    : GSRandomOrder.proposition_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:04:54.125199+00:00
-- url     : https://prove2.me/theorems/27cbf325-188f-47a7-8acd-8bcb3826ce89
-- title:
--   Proposition B.6 — distribution matching: $L_{Q,t}=\mu^v_{Q,t}$
-- statement:
--   Let $v$ be a GS valuation. For every $t\in[1/e,1]$ and $Q\subseteq N$,
--   $$
--   L_{Q,t}=\mu^v_{Q,t}:
--   $$
--   the law of the accepted set of the survival algorithm run on the items of $Q$ alone, with independent arrival times uniform on $[0,t]$, equals the survival law.
--
--   With $Q=N$ and $t=1$ this identifies the law of the algorithm's output.
--
--   **Formalization Note** The two laws are compared at every finite set $A$; both vanish for $A\not\subseteq Q$.
--
--   Differences from the source:
--   - encoding: GS valuation (Definition 2.1, equivalently the exchange axiom (3) by the cited Theorem 2.3, p.6), values in ℝ ∪ {−∞} → IsGSValuation v: v ∅ = 0 and the exchange axiom (3), v : Finset (Fin n) → WithBot ℝ; reason: the paper defines a GS valuation as one with the two equivalent properties and all its proofs use (3); ⊥ = −∞
--   - encoding: equality of two laws on 2^Q → ∀ A, onlineLaw v Q t A = survivalLaw v Q t A; reason: laws on a finite set are equal iff their point masses are
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), Proposition B.6, p.25

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation
import Definitions.Def_GSRandomOrder_survivalLaw
import Definitions.Def_GSRandomOrder_onlineLaw

set_option autoImplicit false

namespace GSRandomOrder

/-- **Proposition B.6 (Distribution matching)** (Paes Leme, Pál, Patel, *Gross Substitutes
Welfare in Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §B.2, p.25). For
every `t ∈ [1/e, 1]` and `Q ⊆ N`, `L_{Q,t} = μ^v_{Q,t}`.

**Formalization Note.** The two laws on subsets of `Q` are compared pointwise: for every finite set
`A`, the probability that the algorithm run on `Q` alone with arrival times uniform on `[0, t]`
accepts exactly `A` (`onlineLaw`) equals `μ^v_{Q,t}(A)` (`survivalLaw`); both are `0` for
`A ⊄ Q`. The proposition is stated for the GS valuation `v` fixed throughout §B (p.21). -/
theorem proposition_B_6 {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (hv : IsGSValuation v)
    (t : ℝ) (ht : t ∈ Set.Icc (Real.exp (-1)) 1) (Q : Finset (Fin n)) :
    ∀ A : Finset (Fin n), onlineLaw v Q t A = survivalLaw v Q t A := by sorry

end GSRandomOrder
