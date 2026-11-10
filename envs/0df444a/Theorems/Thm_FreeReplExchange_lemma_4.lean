-- Prove2me | Theorems.Thm_FreeReplExchange_lemma_4
-- name    : FreeReplExchange.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:18:35.00435+00:00
-- url     : https://prove2.me/theorems/9afb974c-b896-4b12-a98b-a454f1a27332
-- title:
--   Lemma 4 — exact integer weight encoding of the three objectives
-- statement:
--   Assume the sign conditions of §2.1 and fix a global tie order. Consider a round state: an allocation $x\ge x^{(0)}$, a participating set $P$ and a set $D$ of rejected exchanges, whose graph $G_t=(V_t,E_t)$ ($E_t$ the edges of $G(x,P)$ not in $D$, $V_t$ the empty slots of participants) has at least one edge. Let $q=|E_t|$, $h=\lfloor|V_t|/2\rfloor$, list the edges as $f_1,\dots,f_q$ in the inherited global order, and set $\tau(f_\ell)=2^{q-\ell}$, $B=2^q$. Let $Q$ be a positive integer with $z(e)=Q\,g(e)\in\mathbb Z$ for every edge, and define
--   $$A=B(4hQ+1),\qquad w(e)=A+B\,z(e)+\tau(e).$$
--   Then a matching $\mu$ of $G_t$ maximizes $\sum_{e\in\mu}w(e)$ if and only if it is the matching selected by the three optimization objectives of M3.
--
--   A single maximum-weight matching computation therefore implements M3's round rule.
--
--   Differences from the source:
--   - generalization: every good is initially held by at least one agent (WLOG, p.13) → any initial allocation x⁽⁰⁾; reason: no step of the proof uses the assumption; the source's instances are among those covered
--   - encoding: a total order e₁ ≺ ⋯ ≺ e_L on all potential exchanges, fixed independently of participation and history (p.32) → an injective rank rk on exchanges, smaller rank first, fixed before the participating set; reason: every total order on the finite type of exchanges arises from an injective rank, and only the order is used
--   - generalization: a round of M3 whose graph has an edge → any state (x ≥ x⁽⁰⁾, any rejected set D, any P) whose graph E(x,P) ∖ D has an edge; reason: the proof uses only that the edges join empty slots of participants; every round of M3 is such a state
--   - generalization: Q a common positive denominator of the rational utility entries used to compute the edge gains → real utilities and any positive integer Q with Q·g(e) ∈ ℤ for every edge; reason: a common denominator of the entries is such a Q; the proof uses only z(e) ∈ ℤ
--   - encoding: selected by the three optimization objectives of M3 → equal to m3Select, M3's Φ-maximizing matching; reason: for a total order the Φ-maximizer is unique (p.33)
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), p.38 (PDF p.40), §5.4.1, eq. (22), Lemma 4

import Mathlib
import Definitions.Def_FreeReplExchange_m3Select

namespace FreeReplExchange

/-- Lemma 4, Yang–Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with Negative
Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…), p.38 (PDF p.40), with the setup of §5.4.1 on the same page. Fix a
round whose graph `G_t = (V_t, E_t)` has at least one edge, let `q = |E_t|`, `h = ⌊|V_t|/2⌋`, list
the edges as `f_1, …, f_q` in the inherited global order, and set `τ(f_ℓ) = 2^{q−ℓ}`, `B = 2^q`. Let
`Q` be a common positive denominator with `z(e) = Q g(e) ∈ ℤ`, and (22) `A = B(4hQ + 1)`,
`w(e) = A + B z(e) + τ(e)`. A matching maximizes `Σ_{e∈μ} w(e)` iff it is selected by the three
optimization objectives of M3.

**Formalization Note.** The round's state is any allocation `x ≥ x^(0)` and any rejected set `D`,
with `E_t = E(x, P) ∖ D` and `V_t = V(x, P)` (the empty slots of participants). `Q` is any positive
integer with `Q g(e) ∈ ℤ` for every edge (a common denominator of the utility entries used is one).
"Selected by the three objectives" is equality with M3's selection `m3Select`, the unique
`Φ`-maximizer for an injective rank. Weights are computed in `ℝ`; they are integers. -/
theorem lemma_4 {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (hU : SignCond U)
    (rk : Exchange A m → ℕ) (hrk : Function.Injective rk) (P : Finset A)
    (x : A → Fin m → Bool) (hx : Dominates x0 x) (D : Finset (Exchange A m))
    (hE : (edges x0 U P x \ D).Nonempty) (Q : ℕ) (hQ : 0 < Q)
    (hQg : ∀ e ∈ edges x0 U P x \ D, ∃ z : ℤ, (Q : ℝ) * gain U e = z) :
    let E := edges x0 U P x \ D
    let q := E.card
    let h := (Finset.univ.filter fun v : A × Fin m => v.1 ∈ P ∧ x v.1 v.2 = false).card / 2
    let τ : Exchange A m → ℝ := fun e => 2 ^ (q - 1 - (E.filter fun e' => rk e' < rk e).card)
    let B : ℝ := 2 ^ q
    let Acst : ℝ := B * (4 * h * Q + 1)
    let w : Exchange A m → ℝ := fun e => Acst + B * (Q * gain U e) + τ e
    ∀ μ ∈ matchingsOf E,
      ((∀ ν ∈ matchingsOf E, ∑ e ∈ ν, w e ≤ ∑ e ∈ μ, w e) ↔ μ = m3Select U rk E) := by sorry

end FreeReplExchange
