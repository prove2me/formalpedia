-- Prove2me | Theorems.Thm_ObsArrivalPricing_lemma_2
-- name    : ObsArrivalPricing.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:57.807986+00:00
-- url     : https://prove2.me/theorems/7b377a76-1ce2-4379-95db-995d203cea08
-- title:
--   Lemma 2 — a buyer present at a block's end behaves like an observable arrival
-- statement:
--   Fix an instance ($0\le\delta<\mu$, prices in $[0,\bar v]$), $T>0$, $t_0\ge0$ and an admissible price function $p$, and let $\hat p_{t_0}(t)=\hat p(t+t_0)$. Let a buyer with any valuation $v$ arrive at a time $\tau\ge0$ that falls in a block of $\hat p_{t_0}$, i.e. the phase $s$ of $\tau+t_0$ satisfies $s\le T$; he is then present at the end of the block, $b=\tau+(T-s)$, which is the beginning of the next interval $\tilde I_{2k}$ on which $\hat p_{t_0}$ replays $p$. Then
--   $$e^{-\delta b}\,r_{[0,T]}(p,v)\;\le\;r(\hat p_{t_0},\tau,v),$$
--   where $r(\hat p_{t_0},\tau,v)$ is the seller's revenue from this buyer under $\hat p_{t_0}$, and $r_{[0,T]}(p,v)$ is the revenue from a buyer with valuation $v$ arriving at $0$ under $p$ if he purchases by time $T$ (and $0$ otherwise). The left side is the revenue earned up to time $b+T$ in the observable case with arrival time $b$.
--
--   Integrated over $v\sim F$, the seller's expected revenue from $\hat p$ in the unobservable case is at least the expected revenue earned up to time $b+T$ in the observable case with arrival time $b$.
--
--   Differences from the source:
--   - generalization: $p$ is the optimal price function of $[SPO_0]$ ("the price function $p$ comes from the solution of $[SPO_0]$", p.18) → every admissible price function $p$; reason: the bound holds for every admissible $p$, so it contains the printed case of the optimal $p$; the paper never proves that an optimal $p$ exists
--   - generalization: valuation $v\ge p(T)$ → every valuation $v$; reason: for $v<p(T)$ the inequality still holds; the printed case is included
--   - generalization: buyer present at the beginning of $\tilde I_{2k}$ → buyer arriving at any time $\tau$ in the preceding block, compared at the block's end $b$; reason: a buyer arriving at the block's end is the case $\tau=b$
--   - encoding: observable revenue up to time $2kT+t_0$ with arrival time $(2k-1)T+t_0$ (time origin $t_0$ as in Figure 2) → $e^{-\delta b}r_{[0,T]}(p,v)$ pointwise in $v$, with $\hat p_{t_0}(t)=\hat p(t+t_0)$ as in Proposition 3, so the block ends at $b=\tau+T-s$; reason: the observable revenue from an arrival at $b$ is $e^{-\delta b}$ times that from an arrival at $0$ (p.11); the paper's two shift conventions differ only in the sign of $t_0$
--   - reading: (4): $\hat p(2kT)=p(T)$ → $\hat p(2kT)=\min(p(0),p(T))$; reason: as in the definition of $\hat p$; equal for non-increasing $p$
-- source:
--   Correa, Pizarro & Vulcano, The Value of Observing the Buyer Arrival Time in Dynamic Pricing, SSRN 3541494 (rev. Oct 2022), Lemma 2, p.23; proof pp.A6–A7; Figure 2, p.19

import Mathlib
import Definitions.Def_ObsArrivalPricing_PeriodicPolicy

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ObsArrivalPricing

/-- Lemma 2 (SSRN 3541494, p.23; proof pp.A6–A7), for every admissible price function, every
valuation and every arrival during a block. Let `T > 0`, `t0 ≥ 0` and `p` admissible, and let a
buyer with valuation `v` arrive at `τ ≥ 0` while `p̂_{t0}` is in a block (phase `s ≤ T`), so that he
is present at the block's end `b = τ + (T − s)`, the beginning of the next `Ĩ_{2k}`. Then the
seller's revenue under `p̂_{t0}` is at least `e^{−δb}` times the revenue earned up to time `T` from
an observable buyer arriving at `0` under `p`, i.e. the revenue earned up to time `b + T` in the
observable case with arrival time `b`. -/
theorem lemma_2 (I : ProblemInstance) {T : ℝ} (hT : 0 < T) {t0 : ℝ} (ht0 : 0 ≤ t0)
    {p : ℝ → ℝ} (hp : IsAdmissible I.vbar p) (v : ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hblock : phase T (τ + t0) ≤ T) :
    Real.exp (-I.δ * (τ + (T - phase T (τ + t0)))) * revUpTo I.δ I.μ p T v ≤
      rev I.δ I.μ (shiftedPolicy p T t0) τ v := by sorry

end ObsArrivalPricing
