-- Prove2me | Theorems.Thm_FoundationsRL_LinUCB_confidence_ellipsoid_finite
-- name    : FoundationsRL.LinUCB.confidence_ellipsoid_finite
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:22:58.543083+00:00
-- url     : https://prove2.me/theorems/cbf7ed41-8a5c-4c2c-9d51-37bf4c4e8452
-- title:
--   (3.23)–(3.25), p. 44 — the confidence sets of LinUCB lie in the ellipsoids, for finite classes
-- statement:
--   Consider the linear setting with a finite class $\mathcal F$ and $\beta=8\log(|\mathcal F|/\delta)$, $\delta\in(0,1)$, and a run of LinUCB with input $\beta$. Write $\Sigma^t=\sum_{i<t}\phi(x^i,\pi^i)\phi(x^i,\pi^i)^{\top}$. With probability at least $1-\delta$, at every round $t\le T$:
--
--   1. every $\theta\in\Theta$ with $f_\theta\in\mathcal F^t$ satisfies $\|\theta-\theta^\star\|_{\Sigma^t}^2\le4\beta$;
--   2. every $\theta\in\Theta$ with $\|\theta-\theta^\star\|_{\Sigma^t}^2\le4\beta$ satisfies
--
--   $$
--   \|\theta-\widehat\theta^t\|_{\widetilde\Sigma^t}^2\le16\beta+4.
--   $$
--
--   In particular $\theta^\star$, which satisfies the hypothesis of item 2, lies in the ellipsoid used by the algorithm at every round. This is the step that lets LinUCB replace the confidence set by an ellipsoid over all of $\mathbb R^d$.
--
--   Differences from the source:
--   - generalization: $\Pi=\{1,\dots,A\}$ and the filtration $\sigma(\mathcal H^{t-1},x^t)$ → an arbitrary measurable action space and any filtration of a run; reason: the book's setting is an instance.
--   - reading: Proposition 7's proof is silent on $[0,1]$ values → the assumptions of §3.1 are in force (`LinearSetting`); reason: they are the standing assumptions of Lemma 10, which the proof cites.
--   - encoding: the inclusions $\mathcal F^t\subseteq\Theta'\subseteq\Theta''$ → two bad-event clauses, one per inclusion; reason: same content; $\Sigma^t$ is written $\widetilde\Sigma^t-I$.
--   - reading: $M^\star(\cdot\mid x,\pi)$ a conditional distribution and $r^t\in[0,1]$ almost surely → a Markov kernel on the measurable space $\mathcal X\times\Pi$, with $M^\star(\cdot\mid x,\pi)$ carried by $[0,1]$ at every $(x,\pi)$; reason: contexts are arbitrary, so the bound is needed at every pair; with no σ-algebra on $\mathcal X$ the discrete one makes every map measurable.
--   - reading: $\phi$ not said to be measurable → $\phi$ jointly measurable (in `LinearSetting`); reason: the field's standing convention, without which $\phi(x^t,\pi^t)$ is not a random variable.
--   - reading: $\delta$ unquantified → $0<\delta<1$; reason: at $\delta\ge1$ there is nothing to prove.
--   - encoding: rounds $t\in[T]$ → $t<T$ with Lean's round $t$ the book's round $t+1$; reason: Lean indexes rounds from $0$.
--   - encoding: a protocol of $T$ rounds → a run indexed by all of $\mathbb N$; reason: the statement reads only the first $T$ rounds, and a $T$-round run extends to all rounds on a larger probability space.
--   - encoding: probability at least $1-\delta$ → the bad event has outer measure at most $\delta$; reason: no measurability of the event is claimed.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eqs. (3.22)–(3.25), p. 44

import Mathlib
import Definitions.Def_FoundationsRL_LinUCB_linearClass
import Definitions.Def_FoundationsRL_LinUCB_confidenceSet
import Definitions.Def_FoundationsRL_LinUCB_IsLinUCB
import Definitions.Def_FoundationsRL_LinUCB_LinearSetting

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.LinUCB

/-- Eqs. (3.22)–(3.25) (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 44): for a finite class of linear functions and
`β = 8 log(|F|/δ)`, with probability at least `1 − δ`, at every round of LinUCB,

* every `θ ∈ Θ` with `(x, π) ↦ ⟨θ, ϕ(x, π)⟩` in `F^t` has `∥θ − θ⋆∥²_{Σ^t} ≤ 4β` (Eq. (3.23), that is
  `F^t ⊆ Θ′` of Eq. (3.24)), where `Σ^t = Σ̃^t − I`;
* every `θ ∈ Θ′` has `∥θ − θ̂^t∥²_{Σ̃^t} ≤ 16β + 4` (Eq. (3.25), `Θ′ ⊆ Θ″`).

Since `θ⋆ ∈ Θ′`, the true parameter lies in the ellipsoid of every round.

**Formalization Note.** Eq. (3.23) is Eq. (3.10) with the point masses `p^t` of LinUCB. -/
theorem confidence_ellipsoid_finite {Ω X Act : Type*} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace X] [MeasurableSpace Act] (P : Measure Ω) [IsProbabilityMeasure P]
    (Mstar : Kernel (X × Act) ℝ) [IsMarkovKernel Mstar] {d : ℕ}
    (Θ : Set (Fin d → ℝ)) (ϕ : X → Act → Fin d → ℝ) (θstar : Fin d → ℝ)
    (hset : LinearSetting Mstar Θ ϕ θstar) (hF : (linearClass Θ ϕ).Finite)
    (T : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (β : ℝ) (hβ : β = 8 * Real.log ((linearClass Θ ϕ).ncard / δ))
    (R : ContextualBanditRun P Mstar) (thetaHat : ℕ → Ω → Fin d → ℝ)
    (hrun : IsLinUCB Θ ϕ β T R thetaHat) :
    P {ω | ∃ t < T,
        (∃ θ ∈ Θ, linearFunction ϕ θ ∈ confidenceSet (linearClass Θ ϕ) R β t ω ∧
          4 * β < ellipNormSq (designMatrix ϕ R t ω - 1) (θ - θstar)) ∨
        (∃ θ ∈ Θ, ellipNormSq (designMatrix ϕ R t ω - 1) (θ - θstar) ≤ 4 * β ∧
          16 * β + 4 < ellipNormSq (designMatrix ϕ R t ω) (θ - thetaHat t ω))} ≤
      ENNReal.ofReal δ := by sorry

end FoundationsRL.LinUCB
