-- Prove2me | Theorems.Thm_GSRandomOrder_lemma_B_3
-- name    : GSRandomOrder.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:43.445983+00:00
-- url     : https://prove2.me/theorems/135295ea-25de-4927-8990-390e2bc33cc8
-- title:
--   Lemma B.3 — local effect of the moving item
-- statement:
--   In the generalized thought experiment, fix the timestamps $\tau$, let $\tilde\tau\in(1/e,t)$ be different from all the timestamps $\tau_g$ and $\beta_g$, put $U=U_{\tilde\tau}$, and let $f$ be the element of $D_v(U)\setminus D_v(U+x)$ if this set is nonempty (it has at most one element by single displacement). Then $\phi_\tau$ is differentiable at $\tilde\tau$, and
--   $$
--   \bigl(\tilde\tau\,\phi_\tau(\tilde\tau)\bigr)'\ \begin{cases}=-\ln(e\tilde\tau)\,\phi^{-f}_\tau(\tilde\tau)&\text{if }f\text{ is an early item of }S\setminus A,\\ \ge\phi_\tau(\tilde\tau)&\text{otherwise,}\end{cases} \tag{20}
--   $$
--   with equality in the second case if $f$ is a reshuffled item that is not early.
--
--   Delaying $x$ lowers $\tilde\tau\phi_\tau(\tilde\tau)$ exactly when it prolongs the life of an early item outside $A$.
--
--   **Formalization Note** The derivative is with respect to the pinned time of $x$, with $\tau$ fixed. "Otherwise" means that no element of $D_v(U)\setminus D_v(U+x)$ is an early item of $S\setminus A$ (including the case of an empty set).
--
--   Differences from the source:
--   - encoding: GS valuation (Definition 2.1, equivalently the exchange axiom (3) by the cited Theorem 2.3, p.6), values in ℝ ∪ {−∞} → IsGSValuation v: v ∅ = 0 and the exchange axiom (3), v : Finset (Fin n) → WithBot ℝ; reason: the paper defines a GS valuation as one with the two equivalent properties and all its proofs use (3); ⊥ = −∞
--   - encoding: the inputs of the generalized thought experiment and fixed timestamps τ → hypotheses 1/e ≤ t₀ ≤ t ≤ 1, Disjoint S B, β g ∈ [1/e, t] on B, x ∉ S ∪ B, A ⊆ S, τ g ∈ [0, t₀] on S; reason: the experiment's standing inputs (§B.1, pp.21–22)
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), Lemma B.3, p.23, eq. (20)

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation
import Definitions.Def_GSRandomOrder_genMu

set_option autoImplicit false

namespace GSRandomOrder

/-- **Lemma B.3 (Local effect of the moving item)** (Paes Leme, Pál, Patel, *Gross Substitutes
Welfare in Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §B.1, p.23,
eq. (20)). In the generalized thought experiment, fix the timestamps `τ`, let `τ̃ ∈ (1/e, t)` be
different from all the timestamps `τ_g` and `β_g`, put `U = U_τ̃`, and let `f` be the element of
`D_v(U) \ D_v(U + x)` if this set is nonempty (it has at most one element by single
displacement). Then `ϕ_τ` is differentiable at `τ̃`, and
`(τ̃ ϕ_τ(τ̃))′ = −ln(eτ̃) ϕ^{−f}_τ(τ̃)` if `f` is an early item of `S \ A`,
`(τ̃ ϕ_τ(τ̃))′ ≥ ϕ_τ(τ̃)` otherwise (20),
with equality in the second case if `f` is a reshuffled item that is not early.

**Formalization Note.** `φ τ'` is `ϕ_τ(τ')` of (18) with `x` pinned at `τ'`; the prime is
`deriv` of `τ' ↦ τ' · φ τ'` at `τ̃`. `U` is the set present at `τ̃` without `x`. The three cases
are: some `f ∈ D_v(U) \ D_v(U + x)` lies in `S \ A` and is early (`τ_f ≤ 1/e`); no element of
`D_v(U) \ D_v(U + x)` is an early item of `S \ A` ("otherwise", which includes the empty case);
and the equality sub-case, an `f ∈ D_v(U) \ D_v(U + x)` in `S` with `τ_f > 1/e`. The standing
inputs of the experiment are hypotheses, with `τ_g ∈ [0, t₀]` for `g ∈ S`. -/
theorem lemma_B_3 {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (hv : IsGSValuation v)
    (t₀ t : ℝ) (ht₀ : Real.exp (-1) ≤ t₀) (ht₀t : t₀ ≤ t) (ht : t ≤ 1)
    (S B : Finset (Fin n)) (hSB : Disjoint S B) (β : Fin n → ℝ)
    (hβ : ∀ g ∈ B, β g ∈ Set.Icc (Real.exp (-1)) t) (x : Fin n) (hxS : x ∉ S) (hxB : x ∉ B)
    (A : Finset (Fin n)) (hA : A ⊆ S) (τ : Fin n → ℝ) (hτ : ∀ g ∈ S, τ g ∈ Set.Icc 0 t₀)
    (τt : ℝ) (hτt : τt ∈ Set.Ioo (Real.exp (-1)) t) (hτtS : ∀ g ∈ S, τ g ≠ τt)
    (hτtB : ∀ g ∈ B, β g ≠ τt) :
    let U : Finset (Fin n) := presentGen S B β τ τt
    let φ : ℝ → ℝ := fun τ' => genPhi v t S (insert x B) (Function.update β x τ') τ A
    DifferentiableAt ℝ φ τt ∧
    (∀ f ∈ canonicalDemand v U \ canonicalDemand v (insert x U), f ∈ S \ A →
      τ f ≤ Real.exp (-1) →
        deriv (fun τ' => τ' * φ τ') τt =
          -Real.log (Real.exp 1 * τt) *
            genPhiMinus v t S (insert x B) (Function.update β x τt) τ A f) ∧
    ((¬ ∃ f ∈ canonicalDemand v U \ canonicalDemand v (insert x U),
        f ∈ S \ A ∧ τ f ≤ Real.exp (-1)) →
      φ τt ≤ deriv (fun τ' => τ' * φ τ') τt) ∧
    (∀ f ∈ canonicalDemand v U \ canonicalDemand v (insert x U), f ∈ S →
      Real.exp (-1) < τ f → deriv (fun τ' => τ' * φ τ') τt = φ τt) := by sorry

end GSRandomOrder
