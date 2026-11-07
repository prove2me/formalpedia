-- Prove2me | Theorems.Thm_GSRandomOrder_proposition_B_1
-- name    : GSRandomOrder.proposition_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:03.332223+00:00
-- url     : https://prove2.me/theorems/a5d83697-42b7-43bd-9c0f-9c530f3123f6
-- title:
--   Proposition B.1 — comparison inequality, eq. (17)
-- statement:
--   Let $v$ be a GS valuation, $S\subseteq N$, $x\in N\setminus S$ with $x\in D_v(S+x)$, and $t\in[1/e,1]$. Then for every $A\subseteq S$,
--   $$
--   \mu^v_{S,t}(A)\ge\frac1{et}\,\mu^{v/x}_{S,t}(A). \tag{17}
--   $$
--
--   By (9), this says that the acceptance probability of the survival algorithm is at most one, so the algorithm is well defined.
--
--   Differences from the source:
--   - encoding: GS valuation (Definition 2.1, equivalently the exchange axiom (3) by the cited Theorem 2.3, p.6), values in ℝ ∪ {−∞} → IsGSValuation v: v ∅ = 0 and the exchange axiom (3), v : Finset (Fin n) → WithBot ℝ; reason: the paper defines a GS valuation as one with the two equivalent properties and all its proofs use (3); ⊥ = −∞
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), Proposition B.1, p.21, eq. (17)

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation
import Definitions.Def_GSRandomOrder_contract
import Definitions.Def_GSRandomOrder_survivalLaw

set_option autoImplicit false

namespace GSRandomOrder

/-- **Proposition B.1 (Comparison inequality)** (Paes Leme, Pál, Patel, *Gross Substitutes
Welfare in Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §B.1, p.21,
eq. (17)). Let `v` be a GS valuation, `S ⊆ N`, `x ∈ N \ S` with `x ∈ D_v(S + x)`, and
`t ∈ [1/e, 1]`. Then for every `A ⊆ S`, `μ^v_{S,t}(A) ≥ (1/(et)) μ^{v/x}_{S,t}(A)` (17).

**Formalization Note.** `μ^u_{S,t}(A)` is `survivalLaw u S t A`; `v/x` is `contract v x`. By (9)
this says that the acceptance probability of the survival algorithm is at most one. -/
theorem proposition_B_1 {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (hv : IsGSValuation v)
    (S : Finset (Fin n)) (x : Fin n) (hxS : x ∉ S) (hxD : x ∈ canonicalDemand v (insert x S))
    (t : ℝ) (ht : t ∈ Set.Icc (Real.exp (-1)) 1) (A : Finset (Fin n)) (hA : A ⊆ S) :
    1 / (Real.exp 1 * t) * survivalLaw (contract v x) S t A ≤ survivalLaw v S t A := by sorry

end GSRandomOrder
