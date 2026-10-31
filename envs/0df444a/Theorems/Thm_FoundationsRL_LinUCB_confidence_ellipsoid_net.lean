-- Prove2me | Theorems.Thm_FoundationsRL_LinUCB_confidence_ellipsoid_net
-- name    : FoundationsRL.LinUCB.confidence_ellipsoid_net
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:13.474981+00:00
-- url     : https://prove2.me/theorems/761a0500-4175-4557-86bc-6381963c7501
-- title:
--   §3.2, p. 43, and footnote a, p. 44 — the covering argument for infinite classes
-- statement:
--   There is an absolute constant $c>0$ with the following property. Consider the linear setting with an arbitrary, possibly infinite, parameter set $\Theta$, let $d\ge1$, $T\ge2$, and let $\delta\in(0,1)$ satisfy $\log(1/\delta)\le d\log T$. For every run of LinUCB with input $\beta=c\,d\log T$, with probability at least $1-\delta$, at every round $t\le T$,
--
--   $$
--   \|\theta^\star-\widehat\theta^t\|_{\widetilde\Sigma^t}^2\le16\beta+4.
--   $$
--
--   This is the statement that a confidence radius of order $\sqrt{d\log T}$ suffices in place of $\sqrt{\log(|\mathcal F|/\delta)}$, which is what the extension of Proposition 7 to infinite classes rests on.
--
--   Differences from the source:
--   - reading: an $\varepsilon$-discretization with $\varepsilon\sim1/T$ → LinUCB runs on $\Theta$ itself, and the net appears only in the analysis; reason: Proposition 7 keeps the algorithm and changes only $\beta$, and this is the stronger reading, since $\Theta$ may be any set.
--   - reading: no $\delta$ in the clause "we may take $\beta=O(d\log T)$" → every $\delta$ with $\log(1/\delta)\le d\log T$; reason: this is exactly the range where $\log(|N|/\delta)\lesssim d\log T$, and it contains $\delta=1/T$.
--   - generalization: $\Pi=\{1,\dots,A\}$ and the filtration $\sigma(\mathcal H^{t-1},x^t)$ → an arbitrary measurable action space and any filtration of a run; reason: the book's setting is an instance.
--   - reading: "$\beta=O(d\log T)$" → $\beta=c\,d\log T$ for an absolute $c$ and $T\ge2$; reason: at $T=1$ the logarithm vanishes.
--   - reading: the proof of Proposition 7 is silent on $[0,1]$ values → the assumptions of §3.1 are in force (`LinearSetting`); reason: they are the standing assumptions of Lemma 10, which the proof cites.
--   - reading: $M^\star(\cdot\mid x,\pi)$ a conditional distribution and $r^t\in[0,1]$ almost surely → a Markov kernel on the measurable space $\mathcal X\times\Pi$, with $M^\star(\cdot\mid x,\pi)$ carried by $[0,1]$ at every $(x,\pi)$; reason: contexts are arbitrary, so the bound is needed at every pair; with no σ-algebra on $\mathcal X$ the discrete one makes every map measurable.
--   - reading: $\phi$ not said to be measurable → $\phi$ jointly measurable (in `LinearSetting`); reason: the field's standing convention, without which $\phi(x^t,\pi^t)$ is not a random variable.
--   - encoding: rounds $t\in[T]$ → $t<T$ with Lean's round $t$ the book's round $t+1$; reason: Lean indexes rounds from $0$.
--   - encoding: a protocol of $T$ rounds → a run indexed by all of $\mathbb N$; reason: the statement reads only the first $T$ rounds, and a $T$-round run extends to all rounds on a larger probability space.
--   - encoding: probability at least $1-\delta$ → the bad event has outer measure at most $\delta$; reason: no measurability of the event is claimed.
--   - encoding: $\mathbb R^d$ → `Fin d → ℝ` with $0<d$; reason: the book's ambient space has $d\ge1$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §3.2, p. 43; Proposition 7 footnote a, p. 44

import Mathlib
import Definitions.Def_FoundationsRL_LinUCB_IsLinUCB
import Definitions.Def_FoundationsRL_LinUCB_LinearSetting

open MeasureTheory ProbabilityTheory

universe u v w

namespace FoundationsRL.LinUCB

/-- The covering argument for infinite classes (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 43 and footnote a of p. 44): for an
arbitrary `Θ ⊆ B^d_2(1)` there is an absolute `c > 0` such that LinUCB with `β = c d log T`
has `θ⋆` in the ellipsoid `∥θ − θ̂^t∥²_{Σ̃^t} ≤ 16β + 4` of every round, with probability at
least `1 − δ`, for every `δ ≥ T^{−d}`.

**Formalization Note.** LinUCB runs on `Θ` itself; the net appears only in the analysis, where
`ε ∼ 1/T` costs a constant in the confidence width. The condition `log(1/δ) ≤ d log T` is the
range of `δ` for which `log(|N|/δ) ≲ d log T`. -/
theorem confidence_ellipsoid_net : ∃ c : ℝ, 0 < c ∧
    ∀ {Ω : Type u} {X : Type v} {Act : Type w} {mΩ : MeasurableSpace Ω} [MeasurableSpace X]
      [MeasurableSpace Act] (P : Measure Ω) [IsProbabilityMeasure P]
      (Mstar : Kernel (X × Act) ℝ) [IsMarkovKernel Mstar] {d : ℕ}
      (Θ : Set (Fin d → ℝ)) (ϕ : X → Act → Fin d → ℝ) (θstar : Fin d → ℝ),
      LinearSetting Mstar Θ ϕ θstar → 0 < d →
      ∀ (T : ℕ) (δ : ℝ), 2 ≤ T → 0 < δ → δ < 1 → Real.log (1 / δ) ≤ d * Real.log T →
      ∀ (β : ℝ), β = c * d * Real.log T →
      ∀ (R : ContextualBanditRun P Mstar) (thetaHat : ℕ → Ω → Fin d → ℝ),
        IsLinUCB Θ ϕ β T R thetaHat →
        P {ω | ∃ t < T, 16 * β + 4 <
          ellipNormSq (designMatrix ϕ R t ω) (θstar - thetaHat t ω)} ≤ ENNReal.ofReal δ := by sorry

end FoundationsRL.LinUCB
