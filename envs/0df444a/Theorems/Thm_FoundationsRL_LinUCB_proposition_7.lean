-- Prove2me | Theorems.Thm_FoundationsRL_LinUCB_proposition_7
-- name    : FoundationsRL.LinUCB.proposition_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:12.941316+00:00
-- url     : https://prove2.me/theorems/b8795b27-bc99-4017-b1f8-a9181866e164
-- title:
--   Proposition 7 — regret of LinUCB, finite and infinite classes (corrected: $1+\beta$ in place of $\beta$)
-- statement:
--   Let $\Theta\subseteq B_2^d(1)$ and $\phi:\mathcal X\times\Pi\to B_2^d(1)$, with the standing assumptions of §3.1: functions of the class take values in $[0,1]$, rewards lie in $[0,1]$ almost surely, and $f^\star=\langle\theta^\star,\phi\rangle$ for some $\theta^\star\in\Theta$. There are absolute constants $C,c>0$ such that, for any sequence of contexts $x^1,\dots,x^T$, possibly chosen adaptively:
--
--   1. if the class $\mathcal F$ of Eq. (3.21) is finite, $\delta\in(0,1)$ and $\beta=8\log(|\mathcal F|/\delta)$, then LinUCB with input $\beta$ satisfies, with probability at least $1-\delta$,
--
--   $$
--   \mathrm{Reg}\le C\sqrt{(1+\beta)\,d\,T\log(1+T/d)};
--   $$
--
--   2. for an arbitrary, possibly infinite, class, if $T\ge2$, $\delta\in(0,1)$, $\log(1/\delta)\le d\log T$ and $\beta=c\,d\log T$, then LinUCB with input $\beta$ satisfies, with probability at least $1-\delta$,
--
--   $$
--   \mathrm{Reg}\le C\,d\sqrt T\log T.
--   $$
--
--   The bound has no explicit dependence on the number of contexts or on the number of actions: the dimension $d$ takes the place of $|\Pi|$, because the linear structure lets the learner generalize across contexts and across decisions.
--
--   Differences from the source:
--   - correction: $\mathrm{Reg}\lesssim\sqrt{\beta dT\log(1+T/d)}$ → $\mathrm{Reg}\le C\sqrt{(1+\beta)dT\log(1+T/d)}$; reason: the printed bound fails as $\delta\uparrow1$; take $d=2$, $T=1$, $\Theta=\{(1,0)\}$, two actions with features $(1/2,0)$ and $(0,1)$, deterministic rewards: the radius is at least $2$, LinUCB plays the second action with regret $1/2$, and the printed bound tends to $0$. The two forms agree up to $\sqrt2$ once $\beta\ge1$.
--   - reading: Proposition 7 is silent on the range of $f$ and $r$ → $[0,1]$ values as in §3.1, p. 41; reason: the proof applies Lemma 10, and $\Theta,\phi\subseteq B_2^d(1)$ alone gives only $[-1,1]$.
--   - reading: no $\delta$ in the clause "we may take $\beta=O(d\log T)$" → every $\delta$ with $\log(1/\delta)\le d\log T$, that is $\delta\ge T^{-d}$; reason: this contains $\delta=1/T$ and every fixed $\delta$ for large $T$, while for much smaller $\delta$ a fixed multiple of $d\log T$ cannot control the failure probability.
--   - reading: "for infinite $\mathcal F$" with an $\varepsilon$-net → LinUCB runs on $\Theta$ itself; reason: the proposition keeps the algorithm and changes only $\beta$, and this is the stronger reading, since $\Theta$ may be any set.
--   - reading: "$\beta=O(d\log T)$" and "$\lesssim d\sqrt T\log T$" → absolute constants $c$, $C$ with $T\ge2$; reason: at $T=1$ the logarithm vanishes.
--   - generalization: $\Pi=\{1,\dots,A\}$, the filtration $\sigma(\mathcal H^{t-1},x^t)$ and a maximizer $\pi^\star$ → an arbitrary measurable action space, any filtration of a run and $\sup_\pi f^\star(x,\pi)$; reason: the book's setting is an instance, where the supremum is the maximum.
--   - encoding: $\mathbb R^d$ → `Fin d → ℝ` with $0<d$; reason: the bound divides by $d$.
--   - encoding: probability at least $1-\delta$ → the bad event has outer measure at most $\delta$; reason: $\mathrm{Reg}$ contains a supremum over the action space, and no measurability of the event is claimed.
--   - correction: the second bound $\lesssim\sqrt{dT\log(|\mathcal F|/\delta)\log(1+T/d)}$ → no separate clause: it is the corrected bound with $\beta=8\log(|\mathcal F|/\delta)$ written out; reason: the same instance refutes it as $\delta\uparrow1$.
--   - reading: any sequence of contexts $x^1,\dots,x^T$ → contexts adapted to the filtration of the run; reason: p. 38 allows contexts chosen adversarially, and a fixed sequence is the constant case.
--   - reading: $M^\star(\cdot\mid x,\pi)$ a conditional distribution and $r^t\in[0,1]$ almost surely → a Markov kernel on the measurable space $\mathcal X\times\Pi$, with $M^\star(\cdot\mid x,\pi)$ carried by $[0,1]$ at every $(x,\pi)$; reason: contexts are arbitrary, so the bound is needed at every pair; with no σ-algebra on $\mathcal X$ the discrete one makes every map measurable.
--   - reading: $\phi$ not said to be measurable → $\phi$ jointly measurable (in `LinearSetting`); reason: the field's standing convention, without which $\phi(x^t,\pi^t)$ is not a random variable.
--   - encoding: rounds $t\in[T]$ → $t<T$ with Lean's round $t$ the book's round $t+1$; reason: Lean indexes rounds from $0$.
--   - encoding: a protocol of $T$ rounds → a run indexed by all of $\mathbb N$; reason: the statement reads only the first $T$ rounds, and a $T$-round run extends to all rounds on a larger probability space.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 7, p. 44; note on infinite classes, p. 43

import Mathlib
import Definitions.Def_FoundationsRL_LinUCB_regret
import Definitions.Def_FoundationsRL_LinUCB_linearClass
import Definitions.Def_FoundationsRL_LinUCB_IsLinUCB
import Definitions.Def_FoundationsRL_LinUCB_LinearSetting

open MeasureTheory ProbabilityTheory

universe u v w

namespace FoundationsRL.LinUCB

/-- Proposition 7 (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 44), both clauses, with one pair of absolute constants `C, c`.

1. For a finite class `F` of linear functions and `β = 8 log(|F|/δ)`, LinUCB has, with probability
   at least `1 − δ`, `Reg ≤ C √((1 + β) d T log(1 + T/d))` for any sequence of contexts.
2. For an arbitrary, possibly infinite, `Θ`, LinUCB with `β = c d log T` has, with probability at
   least `1 − δ`, `Reg ≤ C d √T log T`, for `T ≥ 2` and `δ ≥ T^{−d}`.

**Formalization Note.** Corrected statement: the book prints `√(β d T log(1 + T/d))`, which is false
as `δ ↑ 1`, because LinUCB's radius `√(16β + 4)` stays at least `2` while `β → 0`. Counterexample with
every assumption: `d = 2`, `T = 1`, `Θ = {(1, 0)}`, two actions with features `(1/2, 0)` and `(0, 1)`,
deterministic rewards: LinUCB plays the second action, with regret `1/2`, while the printed bound
tends to `0`. The two forms agree up to a factor `√2` once `β ≥ 1`. In clause 2 the book names no `δ`
and writes `β = O(d log T)`: it is read here for all `δ` with `log(1/δ) ≤ d log T`, which contains
`δ = 1/T` and any fixed `δ` once `T ≥ (1/δ)^{1/d}`; no fixed multiple of `d log T` can serve
smaller `δ`. "Any sequence of contexts" is `R.x`, which may be adapted to the past. The bad events
are bounded in outer measure, since `Reg` contains a supremum over `Act`. -/
theorem proposition_7 : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    (∀ {Ω : Type u} {X : Type v} {Act : Type w} {mΩ : MeasurableSpace Ω} [MeasurableSpace X]
      [MeasurableSpace Act] (P : Measure Ω) [IsProbabilityMeasure P]
      (Mstar : Kernel (X × Act) ℝ) [IsMarkovKernel Mstar] {d : ℕ}
      (Θ : Set (Fin d → ℝ)) (ϕ : X → Act → Fin d → ℝ) (θstar : Fin d → ℝ),
      LinearSetting Mstar Θ ϕ θstar → 0 < d → (linearClass Θ ϕ).Finite →
      ∀ (T : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
      ∀ (β : ℝ), β = 8 * Real.log ((linearClass Θ ϕ).ncard / δ) →
      ∀ (R : ContextualBanditRun P Mstar) (thetaHat : ℕ → Ω → Fin d → ℝ),
        IsLinUCB Θ ϕ β T R thetaHat →
        P {ω | C * Real.sqrt ((1 + β) * d * T * Real.log (1 + T / d)) < regret R T ω} ≤
          ENNReal.ofReal δ) ∧
    (∀ {Ω : Type u} {X : Type v} {Act : Type w} {mΩ : MeasurableSpace Ω} [MeasurableSpace X]
      [MeasurableSpace Act] (P : Measure Ω) [IsProbabilityMeasure P]
      (Mstar : Kernel (X × Act) ℝ) [IsMarkovKernel Mstar] {d : ℕ}
      (Θ : Set (Fin d → ℝ)) (ϕ : X → Act → Fin d → ℝ) (θstar : Fin d → ℝ),
      LinearSetting Mstar Θ ϕ θstar → 0 < d →
      ∀ (T : ℕ) (δ : ℝ), 2 ≤ T → 0 < δ → δ < 1 → Real.log (1 / δ) ≤ d * Real.log T →
      ∀ (β : ℝ), β = c * d * Real.log T →
      ∀ (R : ContextualBanditRun P Mstar) (thetaHat : ℕ → Ω → Fin d → ℝ),
        IsLinUCB Θ ϕ β T R thetaHat →
        P {ω | C * d * Real.sqrt T * Real.log T < regret R T ω} ≤ ENNReal.ofReal δ) := by sorry

end FoundationsRL.LinUCB
