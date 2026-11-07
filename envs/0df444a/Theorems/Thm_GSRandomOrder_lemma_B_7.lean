-- Prove2me | Theorems.Thm_GSRandomOrder_lemma_B_7
-- name    : GSRandomOrder.lemma_B_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:03:21.492504+00:00
-- url     : https://prove2.me/theorems/bd30e61d-09b0-4552-a294-1dbcd9e25679
-- title:
--   Lemma B.7 — inclusion recursion, eq. (26)
-- statement:
--   Let $v$ be a GS valuation, $Q\subseteq N$, $A\subseteq Q$ and $t\in[1/e,1]$. If $A\ne\emptyset$, then
--   $$
--   m^v_{Q,A}(t)=\sum_{x\in Q\setminus A}\int_{1/e}^{t}m^v_{Q-x,A}(s)\,ds+\sum_{x\in A\cap D_v(Q)}\int_{1/e}^{t}\frac1{es}\,m^{v/x}_{Q-x,A-x}(s)\,ds. \tag{26}
--   $$
--
--   The inclusion masses of the survival law obey the same recursion as those of the online law, which is the core of distribution matching.
--
--   Differences from the source:
--   - encoding: GS valuation (Definition 2.1, equivalently the exchange axiom (3) by the cited Theorem 2.3, p.6), values in ℝ ∪ {−∞} → IsGSValuation v: v ∅ = 0 and the exchange axiom (3), v : Finset (Fin n) → WithBot ℝ; reason: the paper defines a GS valuation as one with the two equivalent properties and all its proofs use (3); ⊥ = −∞
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), Lemma B.7, p.26, eq. (26)

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation
import Definitions.Def_GSRandomOrder_contract
import Definitions.Def_GSRandomOrder_inclusionMass

set_option autoImplicit false

namespace GSRandomOrder

/-- **Lemma B.7 (Inclusion recursion)** (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in
Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §B.2, p.26, eq. (26)). Let `v`
be a GS valuation, `Q ⊆ N`, `A ⊆ Q` and `t ∈ [1/e, 1]`. If `A ≠ ∅`, then
`m^v_{Q,A}(t) = Σ_{x ∈ Q \ A} ∫_{1/e}^{t} m^v_{Q−x,A}(s) ds
  + Σ_{x ∈ A ∩ D_v(Q)} ∫_{1/e}^{t} (1/(es)) m^{v/x}_{Q−x,A−x}(s) ds` (26).

**Formalization Note.** `m^u_{Q,A}(t)` is `inclusionMass u Q A t` (eq. (25)); the integrals are
interval integrals over `[1/e, t]`. No hypothesis on `v/x` is added: for `x ∈ A ∩ D_v(Q)` it is a
GS valuation by Lemma 2.9. -/
theorem lemma_B_7 {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (hv : IsGSValuation v)
    (Q A : Finset (Fin n)) (hAQ : A ⊆ Q) (t : ℝ) (ht : t ∈ Set.Icc (Real.exp (-1)) 1)
    (hA : A.Nonempty) :
    inclusionMass v Q A t =
      (∑ x ∈ Q \ A, ∫ s in Real.exp (-1)..t, inclusionMass v (Q.erase x) A s) +
        ∑ x ∈ A ∩ canonicalDemand v Q, ∫ s in Real.exp (-1)..t,
          1 / (Real.exp 1 * s) * inclusionMass (contract v x) (Q.erase x) (A.erase x) s := by sorry

end GSRandomOrder
