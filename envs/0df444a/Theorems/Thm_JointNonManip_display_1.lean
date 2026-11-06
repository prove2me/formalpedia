-- Prove2me | Theorems.Thm_JointNonManip_display_1
-- name    : JointNonManip.display_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:17.540201+00:00
-- url     : https://prove2.me/theorems/8815bc11-a9ce-4dd5-846a-bf3c0147d545
-- title:
--   Display (1), p.8 — an auxiliary-game equilibrium gives $s=\widetilde y\otimes q\in S_{\mathrm{NE}}$ and $\langle U,e_c\otimes q-s\rangle\le 0$
-- statement:
--   Let $G$ be a finite game with nonempty action sets and learner utilities in $[-1,1]$, let $U\in\mathbb R^{A}$, and let $(\widetilde y,\widetilde x_1,\dots,\widetilde x_{n-1})$ be a mixed Nash equilibrium of the auxiliary game $\widetilde G$ in which the optimizer's utility is $\langle U,y\otimes x_1\otimes\cdots\otimes x_{n-1}\rangle$ and the learners keep $u_1,\dots,u_{n-1}$. Put $q=\bigotimes_i\widetilde x_i$ and $s=\widetilde y\otimes q$. Then
--
--   1. $s\in S_{\mathrm{NE}}(G_{\mathcal L})$;
--   2. for every $c\in A_0$,
--   $$
--   \big\langle U,\ e_c\otimes q-s\big\rangle\le 0 .
--   $$
--
--   With $U=U^{(t)}$ and $c=c^{(t)}$ this is inequality (1), $\langle U^{(t)},k^{(t)}-s^{(t)}\rangle\le0$, the step that drives Lemma 3.2.
--
--   Differences from the source:
--   - generalization: U(t) = ∑_{τ<t} (k(τ) − s(τ)) of Algorithm 1 → any U ∈ ℝ^A; reason: the argument on p.8 uses only that (ỹ(t), x̃(t)) is an equilibrium of G̃(t); the statement specializes to U = U(t) and c = c(t)
--   - encoding: (ỹ(t), x̃(t)) is a mixed Nash equilibrium of G̃(t) → IsAuxNE u U ỹ x̃: ỹ a lottery maximizing ⟨U, y ⊗ q⟩ over lotteries y, and AGT.IsMixedNash (inducedUtility u ỹ) x̃; reason: learner i's payoff in G̃ against ỹ and x̃₋ᵢ is its payoff in G_L(ỹ), and the optimizer's mixed payoff is ⟨U, y ⊗ q⟩; same condition
--   - encoding: learners L = {1, …, n − 1}, finite action sets A₀, Aᵢ (a finite normal-form game, p.4) → a finite type L of learners (empty when n = 1) and finite nonempty types A0, Act i; reason: relabeling; ∆(Aᵢ) is empty unless Aᵢ is nonempty, so nonemptiness is part of the source's model
--   - encoding: CSPs µ ∈ ∆(A) ⊂ ℝ^A, y ⊗ q, ⟨·,·⟩, q = ⊗ᵢ xᵢ ∈ ∆(A_L), ℓ₁ and ℓ₂ norms → real functions on A0 × ((i : L) → Act i); otimes, pairing; AGT.profileProb x of a profile of lotteries AGT.IsLottery; explicit sums l1dist, l2dist; reason: Lean representation of the same objects
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), §3, display (1) and the two sentences before it, p.8

import Mathlib
import Definitions.Def_JointNonManip_Algorithm1

namespace JointNonManip

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-- **Display (1): an equilibrium of the auxiliary game gives a target in `S_NE` and a
nonpositive discrepancy step** (Collina, Fullerton, Liu & Weinberg, *Non-manipulability and
Approachability Beyond Two-Player Games*, manuscript (STOC 2027 submission), §3, display (1),
p.8).

Let `U ∈ ℝ^A` and let `(ỹ, x̃)` be a mixed Nash equilibrium of the auxiliary game `G̃` (optimizer
utility `⟨U, y ⊗ x₁ ⊗ ⋯ ⊗ x_{n−1}⟩`, learner utilities `u₁, …, u_{n−1}`), and `q = ⊗ᵢ x̃ᵢ`. Then
`s = ỹ ⊗ q ∈ S_NE(G_L)` and `⟨U, e_c ⊗ q − s⟩ ≤ 0` for every `c ∈ A₀` (in particular for
`c = c(t)`, which is (1)).

**Formalization Note** "Nash equilibrium of `G̃`" is the unfolded `IsAuxNE`. -/
theorem display_1 [Nonempty A0] [∀ i, Nonempty (Act i)]
    (u : L → A0 × ((i : L) → Act i) → ℝ) (hu : ∀ i a, |u i a| ≤ 1)
    (U : A0 × ((i : L) → Act i) → ℝ) (yt : A0 → ℝ) (xt : (i : L) → Act i → ℝ)
    (hNE : IsAuxNE u U yt xt) :
    otimes yt (AGT.profileProb xt) ∈ SNE u ∧
      ∀ c : A0, pairing U (otimes (pointMass c) (AGT.profileProb xt) -
        otimes yt (AGT.profileProb xt)) ≤ 0 := by sorry

end JointNonManip
