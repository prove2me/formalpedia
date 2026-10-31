-- Prove2me | Theorems.Thm_FoundationsRL_LinUCB_lemma_10
-- name    : FoundationsRL.LinUCB.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:18.213466+00:00
-- url     : https://prove2.me/theorems/0dd443c6-f0dc-43d2-b75f-54f6135799b4
-- title:
--   Lemma 10 — validity of the least-squares confidence sets, for any algorithm
-- statement:
--   Let $\mathcal F$ be a finite class of measurable functions $\mathcal X\times\Pi\to[0,1]$ containing the mean reward function $f^\star$, let rewards lie in $[0,1]$ almost surely, and let $\pi^1,\dots,\pi^T$ be chosen by an arbitrary, possibly randomized, algorithm. Put $\beta=8\log(|\mathcal F|/\delta)$ for $\delta\in(0,1)$. Then with probability at least $1-\delta$, simultaneously:
--
--   1. $f^\star\in\mathcal F^t$ for all $t\in[T]$;
--   2. for all $\tau\le T$, every $f\in\mathcal F^\tau$ satisfies
--
--   $$
--   \sum_{t=1}^{\tau-1}\mathbb E_{\pi^t\sim p^t}\Bigl[\bigl(f(x^t,\pi^t)-f^\star(x^t,\pi^t)\bigr)^2\Bigr]\le4\beta.
--   $$
--
--   The confidence sets therefore contain the truth, and everything in them is close to the truth on the history seen so far, whatever the algorithm does. This is what makes the optimism template of §3.1 work.
--
--   Differences from the source:
--   - generalization: two claims, each with its own event of probability at least $1-\delta$ → one event of probability at least $1-\delta$ on which both hold; reason: the book's proof gets both from the single event (3.18), the printed claims follow, and Proposition 7 needs them together.
--   - generalization: $\Pi=\{1,\dots,A\}$ and the filtration $\sigma(\mathcal H^{t-1},x^t)$ → an arbitrary measurable action space and any filtration of a run; reason: $\{1,\dots,A\}$ with the discrete σ-algebra and the book's filtration are instances.
--   - reading: functions of $\mathcal F$ are not said to be measurable → measurable, jointly in $(x,\pi)$; reason: the field's standing convention, without which $f(x^t,\pi^t)$ is not a random variable.
--   - encoding: rounds $t,\tau\in[T]$ → $t,\tau<T$ with Lean's round $t$ the book's round $t+1$; reason: Lean indexes rounds from $0$.
--   - encoding: probability at least $1-\delta$ → the bad event has outer measure at most $\delta$; reason: no measurability of the event is claimed.
--   - reading: $M^\star(\cdot\mid x,\pi)$ a conditional distribution and $r^t\in[0,1]$ almost surely → a Markov kernel on the measurable space $\mathcal X\times\Pi$, with $M^\star(\cdot\mid x,\pi)$ carried by $[0,1]$ at every $(x,\pi)$; reason: contexts are arbitrary, so the bound is needed at every pair; with no σ-algebra on $\mathcal X$ the discrete one makes every map measurable.
--   - reading: $\delta$ unquantified → $0<\delta<1$; reason: at $\delta\ge1$ there is nothing to prove.
--   - encoding: a protocol of $T$ rounds → a run indexed by all of $\mathbb N$; reason: the statement reads only the first $T$ rounds, and a $T$-round run extends to all rounds on a larger probability space.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 10, Eq. (3.10), p. 41; standing assumptions, p. 41

import Mathlib
import Definitions.Def_FoundationsRL_LinUCB_confidenceSet
import Definitions.Def_FoundationsRL_LinUCB_meanReward

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.LinUCB

/-- Lemma 10 (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 41): validity of the least-squares confidence sets, for an arbitrary and
possibly randomized algorithm. With `β = 8 log(|F|/δ)`, outside an event of probability at most
`δ`: `f⋆ ∈ F^t` for every round, and every `f ∈ F^τ` satisfies
`∑_{t<τ} E_{π^t∼p^t}[(f(x^t, π^t) − f⋆(x^t, π^t))²] ≤ 4β` (Eq. (3.10)).

Lean's rounds `t, τ < T` are the book's rounds `t + 1, τ + 1 ∈ [T]`.

**Formalization Note.** The book states the two claims with two events of probability `1 − δ`.
Its proof derives both from the one event (3.18), and Proposition 7 needs them together at
level `δ`, so one bad event is bounded here, which implies both printed claims. `F` is a finite set
of measurable functions with values in `[0, 1]`, and rewards are in `[0, 1]` almost surely (§3.1,
p. 41). The bad event is bounded in outer measure. -/
theorem lemma_10 {Ω X Act : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace X]
    [MeasurableSpace Act] (P : Measure Ω) [IsProbabilityMeasure P]
    (Mstar : Kernel (X × Act) ℝ) [IsMarkovKernel Mstar]
    (hreward : ∀ z, Mstar z (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (F : Set (X → Act → ℝ)) (hF : F.Finite)
    (hmeas : ∀ f ∈ F, Measurable fun z : X × Act => f z.1 z.2)
    (hrange : ∀ f ∈ F, ∀ x a, f x a ∈ Set.Icc (0 : ℝ) 1)
    (hstar : meanReward Mstar ∈ F)
    (R : ContextualBanditRun P Mstar) (T : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (β : ℝ) (hβ : β = 8 * Real.log (F.ncard / δ)) :
    P {ω | (∃ t < T, meanReward Mstar ∉ confidenceSet F R β t ω) ∨
        ∃ τ < T, ∃ f ∈ confidenceSet F R β τ ω,
          4 * β < ∑ t ∈ Finset.range τ,
            ∫ a, (f (R.x t ω) a - meanReward Mstar (R.x t ω) a) ^ 2 ∂(R.p t ω)} ≤
      ENNReal.ofReal δ := by sorry

end FoundationsRL.LinUCB
