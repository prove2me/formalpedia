-- Prove2me | Theorems.Thm_GSRandomOrder_theorem_B_5
-- name    : GSRandomOrder.theorem_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:55.231257+00:00
-- url     : https://prove2.me/theorems/80610541-a6a0-443f-93d1-50b824d35412
-- title:
--   Theorem B.5 — moving one timestamp: $\tilde\tau\tilde\mu(\tilde\tau)$ is nondecreasing
-- statement:
--   Let $v$ be a GS valuation, and consider the generalized thought experiment with times $1/e\le t_0\le t\le1$, reshuffled items $S$ and pinned items $B$. For every item $x\notin S\cup B$ and every $A\subseteq S$, the function $\tilde\tau\mapsto\tilde\tau\,\tilde\mu(\tilde\tau)$ is nondecreasing on $[1/e,t_0]$. In particular
--   $$
--   \tilde\mu(\tilde\tau)\ge\frac1{e\tilde\tau}\,\tilde\mu(1/e)\qquad(1/e\le\tilde\tau\le t_0). \tag{22}
--   $$
--
--   Evaluated at the two endpoints with $t_0=t$ and no pinned items, this is the comparison inequality.
--
--   Differences from the source:
--   - encoding: GS valuation (Definition 2.1, equivalently the exchange axiom (3) by the cited Theorem 2.3, p.6), values in ℝ ∪ {−∞} → IsGSValuation v: v ∅ = 0 and the exchange axiom (3), v : Finset (Fin n) → WithBot ℝ; reason: the paper defines a GS valuation as one with the two equivalent properties and all its proofs use (3); ⊥ = −∞
--   - encoding: the inputs of the generalized thought experiment → hypotheses 1/e ≤ t₀ ≤ t ≤ 1, Disjoint S B, β g ∈ [1/e, t] on B; reason: the experiment's standing inputs (§B.1, pp.21–22)
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), Theorem B.5, pp.24–25, eq. (22)

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation
import Definitions.Def_GSRandomOrder_genMu

set_option autoImplicit false

namespace GSRandomOrder

/-- **Theorem B.5 (Moving one timestamp)** (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in
Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §B.1, pp.24–25, eq. (22)).
Let `v` be a GS valuation, and consider the generalized thought experiment with times
`t₀ ≤ t`, reshuffled items `S` and pinned items `B`. For every item `x ∉ S ∪ B` and every
`A ⊆ S`, the function `τ̃ ↦ τ̃ μ̃(τ̃)` is nondecreasing on `[1/e, t₀]`. In particular
`μ̃(τ̃) ≥ (1/(eτ̃)) μ̃(1/e)` for `1/e ≤ τ̃ ≤ t₀` (22).

**Formalization Note.** `μ̃ τ̃` is `genMu` with pinned items `B + x` and `β_x = τ̃`. The inputs of
the generalized thought experiment (`1/e ≤ t₀ ≤ t ≤ 1`, `B ∩ S = ∅`, `β_g ∈ [1/e, t]` for
`g ∈ B`) are hypotheses. -/
theorem theorem_B_5 {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (hv : IsGSValuation v)
    (t₀ t : ℝ) (ht₀ : Real.exp (-1) ≤ t₀) (ht₀t : t₀ ≤ t) (ht : t ≤ 1)
    (S B : Finset (Fin n)) (hSB : Disjoint S B) (β : Fin n → ℝ)
    (hβ : ∀ g ∈ B, β g ∈ Set.Icc (Real.exp (-1)) t) (x : Fin n) (hxS : x ∉ S) (hxB : x ∉ B)
    (A : Finset (Fin n)) (hA : A ⊆ S) :
    let μ : ℝ → ℝ := fun τ' => genMu v t₀ t S (insert x B) (Function.update β x τ') A
    MonotoneOn (fun τ' => τ' * μ τ') (Set.Icc (Real.exp (-1)) t₀) ∧
      ∀ τ' ∈ Set.Icc (Real.exp (-1)) t₀, 1 / (Real.exp 1 * τ') * μ (Real.exp (-1)) ≤ μ τ' := by sorry

end GSRandomOrder
