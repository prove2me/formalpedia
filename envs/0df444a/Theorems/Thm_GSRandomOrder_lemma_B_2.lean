-- Prove2me | Theorems.Thm_GSRandomOrder_lemma_B_2
-- name    : GSRandomOrder.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:53.753658+00:00
-- url     : https://prove2.me/theorems/b2fe20ed-e08f-4413-b5ab-dec46508dbf8
-- title:
--   Lemma B.2 — clamp: the death time of an early item as a function of the moving item's timestamp
-- statement:
--   Consider the generalized thought experiment with times $1/e\le t_0\le t\le1$, reshuffled items $S$, pinned items $B$ and a moving item $x\notin S\cup B$, and a set $A\subseteq S$. Fix the timestamps $\tau$ and an early item $g$, and let $a_g=\sigma_g(1/e)$ and $b_g=\sigma_g(t)$ be its death times with $x$ pinned at $1/e$ and at $t$. Then $a_g\le b_g$,
--   $$
--   \sigma_g(\tilde\tau)=\min\{\max\{\tilde\tau,a_g\},b_g\}\qquad(1/e\le\tilde\tau\le t), \tag{19}
--   $$
--   and for $\tilde\tau\in[1/e,t)$ the item $x$ displaces $g$ at time $\tilde\tau$, that is, $g\in D_v(U_{\tilde\tau})\setminus D_v(U_{\tilde\tau}+x)$, exactly when $a_g\le\tilde\tau<b_g$. In particular the intervals $[a_g,b_g)$ of distinct early items are disjoint, each $\sigma_g$ is $1$-Lipschitz, and $\phi_\tau$ is Lipschitz on $[1/e,t]$.
--
--   Moving $x$ affects the death time of an early item only through a clamp, and only one item at a time.
--
--   **Formalization Note** $U_{\tilde\tau}$ is the set present at $\tilde\tau$ without $x$. The fixed timestamps satisfy $\tau_g\in[0,t_0]$. The Lipschitz properties are stated on $[1/e,t]$, where the functions are defined; "Lipschitz" for $\phi_\tau$ asserts some constant.
--
--   Differences from the source:
--   - encoding: GS valuation (Definition 2.1, equivalently the exchange axiom (3) by the cited Theorem 2.3, p.6), values in ℝ ∪ {−∞} → IsGSValuation v: v ∅ = 0 and the exchange axiom (3), v : Finset (Fin n) → WithBot ℝ; reason: the paper defines a GS valuation as one with the two equivalent properties and all its proofs use (3); ⊥ = −∞
--   - encoding: the inputs of the generalized thought experiment and fixed timestamps τ → hypotheses 1/e ≤ t₀ ≤ t ≤ 1, Disjoint S B, β g ∈ [1/e, t] on B, x ∉ S ∪ B, A ⊆ S, τ g ∈ [0, t₀] on S; reason: the experiment's standing inputs (§B.1, pp.21–22)
--   - encoding: each σ_g is 1-Lipschitz → LipschitzOnWith 1 (σ g) on [1/e, t]; reason: σ_g(τ̃) is defined for τ̃ ∈ [1/e, t]
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), Lemma B.2, pp.22–23, eq. (19)

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation
import Definitions.Def_GSRandomOrder_genMu

set_option autoImplicit false

namespace GSRandomOrder

/-- **Lemma B.2 (Clamp)** (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in Random Order*,
STOC 2027 submission, manuscript sha256 69787f50…, §B.1, pp.22–23, eq. (19)).
In the generalized thought experiment (times `1/e ≤ t₀ ≤ t ≤ 1`, reshuffled items `S`, pinned
items `B` disjoint from `S` with timestamps `β_g ∈ [1/e, t]`, moving item `x ∉ S ∪ B`, a set
`A ⊆ S`), fix the timestamps `τ` and an early item `g`, and let `a_g = σ_g(1/e)` and
`b_g = σ_g(t)` be its death times with `x` pinned at `1/e` and at `t`. Then `a_g ≤ b_g`,
`σ_g(τ̃) = min{max{τ̃, a_g}, b_g}` for `1/e ≤ τ̃ ≤ t` (19), and for `τ̃ ∈ [1/e, t)` the item `x`
displaces `g` at time `τ̃`, that is, `g ∈ D_v(U_τ̃) \ D_v(U_τ̃ + x)`, exactly when
`a_g ≤ τ̃ < b_g`. In particular the intervals `[a_g, b_g)` of distinct early items are disjoint,
each `σ_g` is 1-Lipschitz, and `ϕ_τ` is Lipschitz on `[1/e, t]`.

**Formalization Note.** `σ g τ̃` is the death time of `g` with pinned items `B + x` and
`β_x = τ̃` (`Function.update β x τ̃`); `U τ̃` is the set present at `τ̃` *without* `x`; `φ τ̃` is
`ϕ_τ(τ̃)` of (18). The fixed timestamps satisfy `τ_g ∈ [0, t₀]` for `g ∈ S` (they are drawn from
`Unif[0, t₀]`). "Early" is `τ_g ≤ 1/e`. The 1-Lipschitz property of `σ_g` is stated on its domain
`[1/e, t]`; "`ϕ_τ` is Lipschitz" asserts some Lipschitz constant. -/
theorem lemma_B_2 {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (hv : IsGSValuation v)
    (t₀ t : ℝ) (ht₀ : Real.exp (-1) ≤ t₀) (ht₀t : t₀ ≤ t) (ht : t ≤ 1)
    (S B : Finset (Fin n)) (hSB : Disjoint S B) (β : Fin n → ℝ)
    (hβ : ∀ g ∈ B, β g ∈ Set.Icc (Real.exp (-1)) t) (x : Fin n) (hxS : x ∉ S) (hxB : x ∉ B)
    (A : Finset (Fin n)) (hA : A ⊆ S) (τ : Fin n → ℝ) (hτ : ∀ g ∈ S, τ g ∈ Set.Icc 0 t₀) :
    let σ : Fin n → ℝ → ℝ := fun g τ' =>
      deathTime v (presentGen S (insert x B) (Function.update β x τ') τ) t g
    let U : ℝ → Finset (Fin n) := presentGen S B β τ
    let φ : ℝ → ℝ := fun τ' => genPhi v t S (insert x B) (Function.update β x τ') τ A
    (∀ g ∈ S, τ g ≤ Real.exp (-1) →
      σ g (Real.exp (-1)) ≤ σ g t ∧
      (∀ τ' ∈ Set.Icc (Real.exp (-1)) t,
        σ g τ' = min (max τ' (σ g (Real.exp (-1)))) (σ g t)) ∧
      (∀ τ' ∈ Set.Ico (Real.exp (-1)) t,
        (g ∈ canonicalDemand v (U τ') ∧ g ∉ canonicalDemand v (insert x (U τ'))) ↔
          (σ g (Real.exp (-1)) ≤ τ' ∧ τ' < σ g t)) ∧
      LipschitzOnWith 1 (σ g) (Set.Icc (Real.exp (-1)) t)) ∧
    (∀ g ∈ S, ∀ h ∈ S, τ g ≤ Real.exp (-1) → τ h ≤ Real.exp (-1) → g ≠ h →
      Disjoint (Set.Ico (σ g (Real.exp (-1))) (σ g t)) (Set.Ico (σ h (Real.exp (-1))) (σ h t))) ∧
    ∃ K, LipschitzOnWith K φ (Set.Icc (Real.exp (-1)) t) := by sorry

end GSRandomOrder
