-- Prove2me | Theorems.Thm_GSRandomOrder_lemma_B_4
-- name    : GSRandomOrder.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:34.467806+00:00
-- url     : https://prove2.me/theorems/7408b924-8161-4c73-b327-adfcc6b5d681
-- title:
--   Lemma B.4 — cost and repayment, eq. (21)
-- statement:
--   Consider the generalized thought experiment with times $\tilde\tau<t\le1$, where $\tilde\tau>1/e$, reshuffled items $S$, pinned items $B$ none of which is pinned at $\tilde\tau$, a moving item $x$, and a set $A\subseteq S$. Let $U=S\cup B_{\tilde\tau}$ be the set present at time $\tilde\tau$, and suppose that $D_v(U)\setminus D_v(U+x)=\{f\}$ with $f\in S\setminus A$. Let $\tilde\mu_f$ be the function $\tilde\mu$ of the generalized thought experiment with times $\tilde\tau<t$, reshuffled items $S-f$, pinned items $B+x$ with $x$ pinned at $\tilde\tau$, moving item $f$, and the set $A$. Then
--   $$
--   \mathbb E\bigl[(\tilde\tau\phi_\tau(\tilde\tau))'\bigr]=\frac1{\tilde\tau}\int_{1/e}^{\tilde\tau}\tilde\mu_f(\tau_f)\,d\tau_f-\frac{\ln(e\tilde\tau)}{e\tilde\tau}\,\tilde\mu_f(1/e)=\frac1{\tilde\tau}\int_{1/e}^{\tilde\tau}\Bigl(\tilde\mu_f(\tau_f)-\frac{\tilde\mu_f(1/e)}{e\tau_f}\Bigr)d\tau_f. \tag{21}
--   $$
--
--   The early timestamps of $f$ cost $\frac{\ln(e\tilde\tau)}{e\tilde\tau}\tilde\mu_f(1/e)$ and the late ones repay $\frac1{\tilde\tau}\int\tilde\mu_f$; the logarithmic retention law makes the two terms comparable under one integral.
--
--   **Formalization Note** "Times $\tilde\tau<t$" means $t_0=\tilde\tau$: the reshuffled timestamps are uniform on $[0,\tilde\tau]$. The expectation is over these timestamps of the derivative with respect to the pinned time of $x$; the derivative exists outside a null set of timestamps (Lemma B.3), and Lean's default value of the derivative there does not change the expectation.
--
--   Differences from the source:
--   - encoding: GS valuation (Definition 2.1, equivalently the exchange axiom (3) by the cited Theorem 2.3, p.6), values in ℝ ∪ {−∞} → IsGSValuation v: v ∅ = 0 and the exchange axiom (3), v : Finset (Fin n) → WithBot ℝ; reason: the paper defines a GS valuation as one with the two equivalent properties and all its proofs use (3); ⊥ = −∞
--   - encoding: E[(τ̃ϕ_τ(τ̃))′] over τ ∼ Unif[0, τ̃]^S → ∫ over r ∈ [0,1]^n of deriv (τ' ↦ τ' · ϕ_{τ̃ r}(τ')) at τ̃; reason: rescaled uniform timestamps; deriv's default value lives on a null set
--   - encoding: the inputs of the generalized thought experiment → hypotheses 1/e < τ̃ < t ≤ 1, Disjoint S B, β g ∈ [1/e, t] and β g ≠ τ̃ on B, x ∉ S ∪ B, A ⊆ S; reason: the experiment's standing inputs (§B.1, pp.21–22) and the lemma's hypotheses
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), Lemma B.4, pp.23–24, eq. (21)

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation
import Definitions.Def_GSRandomOrder_genMu

set_option autoImplicit false

open MeasureTheory

namespace GSRandomOrder

/-- **Lemma B.4 (Cost and repayment)** (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in
Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §B.1, pp.23–24, eq. (21)).
Consider the generalized thought experiment with times `τ̃ < t`, where `τ̃ > 1/e`, reshuffled
items `S`, pinned items `B` none of which is pinned at `τ̃`, a moving item `x`, and a set `A ⊆ S`.
Let `U = S ∪ B_τ̃` be the set present at time `τ̃`, and suppose that `D_v(U) \ D_v(U + x) = {f}`
with `f ∈ S \ A`. Let `μ̃_f` be the function `μ̃` of the generalized thought experiment with times
`τ̃ < t`, reshuffled items `S − f`, pinned items `B + x` with `x` pinned at `τ̃`, moving item `f`,
and the set `A`. Then
`E[(τ̃ϕ_τ(τ̃))′] = (1/τ̃) ∫_{1/e}^{τ̃} μ̃_f(τ_f) dτ_f − (ln(eτ̃)/(eτ̃)) μ̃_f(1/e)
  = (1/τ̃) ∫_{1/e}^{τ̃} (μ̃_f(τ_f) − μ̃_f(1/e)/(eτ_f)) dτ_f` (21).

**Formalization Note.** "Times `τ̃ < t`" is `t₀ = τ̃`: the reshuffled timestamps are
`τ_g = τ̃ · r_g`, uniform on `[0, τ̃]`, and the expectation is the integral over
`r : Fin n → unitInterval`. The derivative `(τ̃ϕ_τ(τ̃))′` (with respect to the pinned time of `x`,
`τ` fixed) is `deriv`; it exists for almost every `τ` (Lemma B.3: off the null set where some
`τ_g = τ̃`), and Lean's junk value of `deriv` off the differentiability set is on a null set, so
it does not affect the expectation. `μ̃_f(τ_f)` is `genMu` with pinned items `B + x + f` and
`β_x = τ̃`, `β_f = τ_f`. The standing inputs (`B ∩ S = ∅`, `β_g ∈ [1/e, t]` on `B`, `t ≤ 1`) are
hypotheses. -/
theorem lemma_B_4 {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (hv : IsGSValuation v)
    (τt t : ℝ) (hτt : Real.exp (-1) < τt) (hτtt : τt < t) (ht : t ≤ 1)
    (S B : Finset (Fin n)) (hSB : Disjoint S B) (β : Fin n → ℝ)
    (hβ : ∀ g ∈ B, β g ∈ Set.Icc (Real.exp (-1)) t) (hβτt : ∀ g ∈ B, β g ≠ τt)
    (x : Fin n) (hxS : x ∉ S) (hxB : x ∉ B) (A : Finset (Fin n)) (hA : A ⊆ S) (f : Fin n)
    (hf : canonicalDemand v (S ∪ presentAt B β τt) \
        canonicalDemand v (insert x (S ∪ presentAt B β τt)) = {f})
    (hfA : f ∈ S \ A) :
    let μf : ℝ → ℝ := fun τf =>
      genMu v τt t (S.erase f) (insert f (insert x B))
        (Function.update (Function.update β x τt) f τf) A
    let E : ℝ := ∫ r : Fin n → unitInterval,
      deriv (fun τ' => τ' * genPhi v t S (insert x B) (Function.update β x τ')
        (fun g => τt * (r g : ℝ)) A) τt
    E = 1 / τt * (∫ τf in Real.exp (-1)..τt, μf τf) -
        Real.log (Real.exp 1 * τt) / (Real.exp 1 * τt) * μf (Real.exp (-1)) ∧
    E = 1 / τt * ∫ τf in Real.exp (-1)..τt, (μf τf - μf (Real.exp (-1)) / (Real.exp 1 * τf)) := by sorry

end GSRandomOrder
