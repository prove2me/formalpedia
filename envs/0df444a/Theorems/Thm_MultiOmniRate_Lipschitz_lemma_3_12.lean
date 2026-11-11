-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_lemma_3_12
-- name    : MultiOmniRate.Lipschitz.lemma_3_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:24:21.050496+00:00
-- url     : https://prove2.me/theorems/eddf4979-8ecf-4c18-b546-f9892a908f75
-- title:
--   Lemma 3.12 — signed exponential weights: regret $Ca\sqrt{n\log(2M)}$, and $Ca\sqrt{n\log(2M/\delta)}$ for conditional means w.p. $1-\delta$
-- statement:
--   Let $\mathcal B$ consist of $M\ge1$ tests $b$ with $\|b\|_\infty\le a$, $a>0$, and run Algorithm 2, $\mathrm{EW}(\mathcal B,a,n)$, with weights $\lambda_t(b,s)$. There is an absolute constant $C$ such that, for every horizon $n\ge1$:
--
--   1. for every sequence of payoffs $\rho_t(b)\in[-2a,2a]$,
--   $$\max_{b\in\mathcal B}\Big|\sum_{t=1}^n\rho_t(b)\Big|\le\sum_{t=1}^n\sum_{b\in\mathcal B}\sum_{s\in\{-1,1\}}\lambda_t(b,s)\,s\,\rho_t(b)+Ca\sqrt{n\log(2M)};$$
--   2. its outputs satisfy $\|b_t\|_\infty\le a$;
--   3. for random payoffs, let $\bar\rho_t(b)$ be the conditional mean of $\rho_t(b)$ given the preceding rounds and all choices made before the current payoff vector is sampled (so $\lambda_t$ is fixed). For every $0<\delta<1$, with probability at least $1-\delta$,
--   $$\max_{b\in\mathcal B}\Big|\sum_{t=1}^n\bar\rho_t(b)\Big|\le\sum_{t=1}^n\sum_{b}\sum_{s}\lambda_t(b,s)\,s\,\bar\rho_t(b)+Ca\sqrt{n\log(2M/\delta)},$$
--   the algorithm still updating with the observed payoffs $\rho_t(b)$.
--
--   This is the finite-test learner from which the chaining learners of Algorithms 3 and 4 are assembled.
--
--   Differences from the source:
--   - encoding: rounds $t=1,\dots,n$ → rounds $t=0,\dots,n-1$ (`Finset.range n` or `Fin n`); reason: index shift only
--   - encoding: the $M$ tests of $\mathcal B$; signs $s\in\{-1,1\}$ → a family indexed by a finite nonempty type `ι` with $M=|ι|$; signs as `Bool` with `sgn true = 1`, `sgn false = -1`; reason: the bound depends on $\mathcal B$ only through $M$
--   - reading: "For random payoffs, condition on the preceding rounds and all choices made before the current payoff vector is sampled" → a filtration $(\mathcal F_t)$ on a probability space with $\rho_t$ $\mathcal F_{t+1}$-measurable, $\bar\rho_t=\mathbb E[\rho_t\mid\mathcal F_t]$, $\lambda_t$ computed from the observed $\rho_0,\dots,\rho_{t-1}$; "with probability at least $1-\delta$" as: the failure set has (outer) measure at most $\delta$; reason: the filtration is the conditioning the lemma describes; the outer measure needs no measurability of the event
--   - encoding: "Its outputs satisfy $\|b_t\|_\infty\le a$" → $|b_t(z)_k|\le a$ for every round $t$, point $z$, coordinate $k$ and payoff sequence; reason: pointwise form of the sup norm
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), p. 33, Lemma 3.12 (proof: pp. 57–58, App. A.3)

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_Smoothing
import Definitions.Def_MultiOmniRate_Lipschitz_Learners

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem lemma_3_12 : ∃ C : ℝ, 0 < C ∧
    ∀ (K : ℕ) (ι Z : Type*) [Fintype ι] [Nonempty ι] (b : ι → Z → Fin K → ℝ) (a : ℝ), 0 < a →
      (∀ i z k, |b i z k| ≤ a) → ∀ n : ℕ, 1 ≤ n →
      (∀ ρ : ℕ → ι → ℝ, (∀ t < n, ∀ i, |ρ t i| ≤ 2 * a) →
        (⨆ i, |∑ t ∈ Finset.range n, ρ t i|) ≤
          ∑ t ∈ Finset.range n, ∑ i, ∑ s : Bool,
              ewWeight (ewEta (Fintype.card ι) a n) ρ t i s * sgn s * ρ t i +
            C * a * Real.sqrt (n * Real.log (2 * (Fintype.card ι : ℝ)))) ∧
      (∀ (ρ : ℕ → ι → ℝ) (t : ℕ) (z : Z) (k : Fin K),
        |ewOut b (ewWeight (ewEta (Fintype.card ι) a n) ρ t) z k| ≤ a) ∧
      (∀ (Ω : Type*) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (ℱ : Filtration ℕ mΩ) (ρ : ℕ → Ω → ι → ℝ),
          (∀ t i, Measurable[ℱ (t + 1)] (fun ω => ρ t ω i)) →
          (∀ t < n, ∀ ω i, |ρ t ω i| ≤ 2 * a) →
          ∀ δ : ℝ, 0 < δ → δ < 1 →
            P {ω | ¬ ((⨆ i, |∑ t ∈ Finset.range n, condExp (ℱ t) P (fun ω' => ρ t ω' i) ω|) ≤
              ∑ t ∈ Finset.range n, ∑ i, ∑ s : Bool,
                  ewWeight (ewEta (Fintype.card ι) a n) (fun t' => ρ t' ω) t i s * sgn s *
                    condExp (ℱ t) P (fun ω' => ρ t ω' i) ω +
                C * a * Real.sqrt (n * Real.log (2 * (Fintype.card ι : ℝ) / δ)))} ≤
              ENNReal.ofReal δ) := by sorry

end MultiOmniRate.Lipschitz
