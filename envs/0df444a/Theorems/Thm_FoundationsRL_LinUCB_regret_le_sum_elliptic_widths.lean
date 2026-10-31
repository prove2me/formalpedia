-- Prove2me | Theorems.Thm_FoundationsRL_LinUCB_regret_le_sum_elliptic_widths
-- name    : FoundationsRL.LinUCB.regret_le_sum_elliptic_widths
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:29.943143+00:00
-- url     : https://prove2.me/theorems/2aab423d-1b30-4650-843f-1a8e26adcfec
-- title:
--   (3.27), p. 45 — regret at most the sum of elliptic widths (corrected: explicit $\sqrt{16\beta+4}$ in place of $\lesssim\sqrt\beta$)
-- statement:
--   Consider the linear setting and a run of LinUCB with input $\beta\ge0$. On the event that $\theta^\star$ lies in the ellipsoid $\|\theta-\widehat\theta^t\|_{\widetilde\Sigma^t}^2\le16\beta+4$ at every round $t\le T$,
--
--   $$
--   \mathrm{Reg}\le2\sqrt{16\beta+4}\ \sum_{t=1}^T\|\phi(x^t,\pi^t)\|_{(\widetilde\Sigma^t)^{-1}}\le2\sqrt{(16\beta+4)\,T\sum_{t=1}^T\|\phi(x^t,\pi^t)\|_{(\widetilde\Sigma^t)^{-1}}^2}.
--   $$
--
--   This is the optimism step: the instantaneous regret is at most the width of the confidence interval at the played action. Together with the elliptic potential lemma it gives the rate of Proposition 7.
--
--   Differences from the source:
--   - correction: the final $\lesssim\sqrt{\beta T\sum\cdots}$ → the explicit $2\sqrt{(16\beta+4)T\sum\cdots}$; reason: the printed form fails as $\beta\to0$, because the radius $\sqrt{16\beta+4}$ stays at least $2$; in the instance $d=2$, $T=1$, $\Theta=\{(1,0)\}$, features $(1/2,0)$ and $(0,1)$, deterministic rewards, the regret is $1/2$ and the width $1$ for every $\beta$.
--   - generalization: $\Pi=\{1,\dots,A\}$ → an arbitrary measurable action space; reason: $\{1,\dots,A\}$ with the discrete σ-algebra is an instance.
--   - encoding: an inequality on the event of Proposition 7's proof → a statement at a fixed $\omega$ under the hypothesis that $\theta^\star$ is in every ellipsoid; reason: the step is pathwise.
--   - generalization: input $\beta>0$ → $\beta\ge0$; reason: every positive input is an instance.
--   - generalization: the filtration $\sigma(\mathcal H^{t-1},x^t)$ and a maximizer $\pi^\star$ → any filtration of a run and $\sup_\pi f^\star(x,\pi)$; reason: the book's setting is an instance, where the supremum is the maximum.
--   - reading: the proof of Proposition 7 is silent on $[0,1]$ values → the assumptions of §3.1 are in force (`LinearSetting`); reason: they are the standing assumptions of Lemma 10, which the proof cites.
--   - reading: $M^\star(\cdot\mid x,\pi)$ a conditional distribution and $r^t\in[0,1]$ almost surely → a Markov kernel on the measurable space $\mathcal X\times\Pi$, with $M^\star(\cdot\mid x,\pi)$ carried by $[0,1]$ at every $(x,\pi)$; reason: contexts are arbitrary, so the bound is needed at every pair; with no σ-algebra on $\mathcal X$ the discrete one makes every map measurable.
--   - reading: $\phi$ not said to be measurable → $\phi$ jointly measurable (in `LinearSetting`); reason: the field's standing convention, without which $\phi(x^t,\pi^t)$ is not a random variable.
--   - encoding: rounds $t\in[T]$ → $t<T$ with Lean's round $t$ the book's round $t+1$; reason: Lean indexes rounds from $0$.
--   - encoding: a protocol of $T$ rounds → a run indexed by all of $\mathbb N$; reason: the statement reads only the first $T$ rounds, and a $T$-round run extends to all rounds on a larger probability space.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eq. (3.27), p. 45

import Mathlib
import Definitions.Def_FoundationsRL_LinUCB_regret
import Definitions.Def_FoundationsRL_LinUCB_IsLinUCB
import Definitions.Def_FoundationsRL_LinUCB_LinearSetting

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.LinUCB

/-- Eq. (3.27) (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 45): on the event that `θ⋆` lies in every ellipsoid of the algorithm, the regret
of LinUCB is at most the sum of the elliptic widths,
`Reg ≤ 2 √(16β + 4) ∑_t ∥ϕ(x^t, π^t)∥_{(Σ̃^t)⁻¹} ≤ 2 √((16β + 4) T ∑_t ∥ϕ(x^t, π^t)∥²_{(Σ̃^t)⁻¹})`.

**Formalization Note.** A pathwise statement at a fixed `ω`: the event is the hypothesis `hconf`.
The book's last step reads `≲ √(βT ∑ …)`, which fails as `β → 0` (the radius is at least `2`); the
exact constant `2 √(16β + 4)` of the book's first inequality is kept. -/
theorem regret_le_sum_elliptic_widths {Ω X Act : Type*} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace X] [MeasurableSpace Act] (P : Measure Ω) [IsProbabilityMeasure P]
    (Mstar : Kernel (X × Act) ℝ) [IsMarkovKernel Mstar] {d : ℕ}
    (Θ : Set (Fin d → ℝ)) (ϕ : X → Act → Fin d → ℝ) (θstar : Fin d → ℝ)
    (hset : LinearSetting Mstar Θ ϕ θstar)
    (β : ℝ) (hβ : 0 ≤ β) (T : ℕ) (R : ContextualBanditRun P Mstar)
    (thetaHat : ℕ → Ω → Fin d → ℝ) (hrun : IsLinUCB Θ ϕ β T R thetaHat) (ω : Ω)
    (hconf : ∀ t < T,
      ellipNormSq (designMatrix ϕ R t ω) (θstar - thetaHat t ω) ≤ 16 * β + 4) :
    regret R T ω ≤
        2 * Real.sqrt (16 * β + 4) * ∑ t ∈ Finset.range T,
          Real.sqrt (ellipNormSq (designMatrix ϕ R t ω)⁻¹ (ϕ (R.x t ω) (R.act t ω))) ∧
      2 * Real.sqrt (16 * β + 4) * ∑ t ∈ Finset.range T,
          Real.sqrt (ellipNormSq (designMatrix ϕ R t ω)⁻¹ (ϕ (R.x t ω) (R.act t ω))) ≤
        2 * Real.sqrt ((16 * β + 4) * T * ∑ t ∈ Finset.range T,
          ellipNormSq (designMatrix ϕ R t ω)⁻¹ (ϕ (R.x t ω) (R.act t ω))) := by sorry

end FoundationsRL.LinUCB
