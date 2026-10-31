-- Prove2me | Theorems.Thm_FoundationsRL_LSVI_lemma_25
-- name    : FoundationsRL.LSVI.lemma_25
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:24.310976+00:00
-- url     : https://prove2.me/theorems/f2c45d3a-e5c7-4583-bbe7-8ffb9ddf098c
-- title:
--   Lemma 25, p. 132 — in a low-rank MDP, Bellman backups of arbitrary functions are linear in $\phi$
-- statement:
--   Let $M$ be a low-rank MDP with features $\phi:\mathcal S\times\mathcal A\to\mathbb R^d$ and horizon $H$, and let $h\in[H]$.
--
--   1. For every $Q:\mathcal S\times\mathcal A\to\mathbb R$ for which $\mathcal T^M_hQ$ is defined (each $Q(s',\cdot)$ bounded above and the series $\sum_{s'}P^M_h(s'\mid s,a)\max_{a'}Q(s',a')$ convergent), there is $\theta^M_Q\in\mathbb R^d$ with
--   $$
--   [\mathcal T^M_hQ](s,a)=\langle\phi(s,a),\theta^M_Q\rangle\qquad\text{for all }(s,a).
--   $$
--   2. For every randomized non-stationary policy $\pi$, the function $Q^{M,\pi}_h$ is linear in $\phi$.
--   3. For every $Q:\mathcal S\times\mathcal A\to[0,1]$, the vector $\theta^M_Q$ in part 1 can be taken with $\|\theta^M_Q\|_2\le2\sqrt d$.
--
--   The lemma is why least squares on the features can fit Bellman backups of the algorithm's own estimates: the targets of LSVI-UCB's regression are always linear in $\phi$, with a parameter of norm at most $2\sqrt d$.
--
--   Differences from the source:
--   - encoding: state space S, transitions summed as Σ_{s'} (p. 132), A large or infinite → S a countable type with P^M_h(· | s, a) a probability mass function; A an arbitrary type; reason: the book's Σ_{s'} presupposes a countable S; no finiteness is assumed
--   - reading: "for any Q : S × A → ℝ", with T^M_h Q given by (7.4) → Q with Q(s', ·) bounded above at every s' and Σ_{s'} P^M_h(s' | s, a) sup_{a'} Q(s', a') convergent at every (s, a); reason: exactly the Q for which (7.4) is defined when S is countable and A may be infinite; for other Q the book's expression is undefined
--   - generalization: max_{a'} Q(s', a') → sup_{a'} Q(s', a'); reason: equal whenever the maximum exists, so the statement covers every Q for which the book's maximum exists
--   - encoding: θ^M_Q and the bound ‖θ^M_Q‖ ≤ 2√d for Q : S × A → [0, 1] → for such Q, some θ with T^M_h Q = ⟨ϕ, θ⟩ and ‖θ‖ ≤ 2√d; reason: θ^M_Q is not unique when the features do not span ℝ^d; the book's vector (7.6) is one such θ
--   - encoding: π = (π₁, …, π_H) ∈ Π_rns and Q^{M,π}_h as an expected reward-to-go → π_h(s) a probability measure on a σ-algebra on A, and Q^{M,π}_h by the policy recursion (EpisodicMDP.Qpi); reason: the recursion is the standard form of the conditional expectation on p. 82
--   - reading: "both cumulative and individual-step rewards are in [0, 1]" (pp. 129, 132), with no statement of where the cumulative bound holds → the cumulative bound holds from every state at every layer (IsLowRank.cumulative); reason: the proof of Lemma 28 (p. 137) uses Q^{M,⋆}_h ≤ 1 at every (s, a, h); read from the initial distribution only, this can fail at states d₁ never reaches
--   - generalization: Σ_h r_h ∈ [0, 1] almost surely → Q^{M,⋆}_h(s, a) ≤ 1 for every h ∈ [H] and (s, a); reason: Q^{M,⋆}_h is the largest expected reward-to-go, so the almost-sure bound implies it; only this consequence is used
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 25, p. 132, with (7.4)–(7.7)

import Mathlib
import Definitions.Def_FoundationsRL_LSVI_EpisodicMDP
import Definitions.Def_FoundationsRL_LSVI_IsLowRank

open MeasureTheory

namespace FoundationsRL.LSVI

/-- **Lemma 25** (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision
Making*, arXiv:2312.16730v1, Lemma 25, p. 132): in a low-rank MDP, Bellman backups of arbitrary
functions are linear in `ϕ`. For every `h ∈ [H]`:

1. for every `Q : S × A → ℝ` for which `T^M_h Q` is defined, `[T^M_h Q](s, a) = ⟨ϕ(s, a), θ^M_Q⟩`
   for some `θ^M_Q ∈ ℝ^d`;
2. for every policy `π ∈ Π_rns`, `Q^{M,π}_h` is linear in `ϕ`;
3. for every `Q : S × A → [0, 1]`, such a `θ^M_Q` exists with `‖θ^M_Q‖ ≤ 2√d`.

**Formalization Note.** "`T^M_h Q` is defined" is: `max_{a'} Q(s', a')` exists as a supremum
(`Q(s', ·)` bounded above) and the series `Σ_{s'} P^M_h(s' | s, a) max_{a'} Q(s', a')` converges at
every `(s, a)`. -/
theorem lemma_25 {S A : Type*} [Countable S] [MeasurableSpace A] {d H : ℕ}
    (M : EpisodicMDP S A) (ϕ : S → A → EuclideanSpace ℝ (Fin d)) (hM : IsLowRank M H ϕ) :
    (∀ h ∈ Finset.Icc 1 H, ∀ Q : S → A → ℝ, (∀ s', BddAbove (Set.range (Q s'))) →
      (∀ s a, Summable fun s' => (M.P h s a s').toReal * ⨆ a', Q s' a') →
      ∃ θ : EuclideanSpace ℝ (Fin d), ∀ s a, M.bellman h Q s a = inner ℝ (ϕ s a) θ) ∧
    (∀ π : EpisodicMDP.MarkovPolicy S A, ∀ h ∈ Finset.Icc 1 H,
      ∃ θ : EuclideanSpace ℝ (Fin d), ∀ s a, M.Qpi H π h s a = inner ℝ (ϕ s a) θ) ∧
    (∀ h ∈ Finset.Icc 1 H, ∀ Q : S → A → ℝ, (∀ s a, Q s a ∈ Set.Icc (0 : ℝ) 1) →
      ∃ θ : EuclideanSpace ℝ (Fin d),
        (∀ s a, M.bellman h Q s a = inner ℝ (ϕ s a) θ) ∧ ‖θ‖ ≤ 2 * Real.sqrt d) := by sorry

end FoundationsRL.LSVI
