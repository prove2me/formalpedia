-- Prove2me | Theorems.Thm_OfflineRLFastRates_bi_indicator
-- name    : OfflineRLFastRates.bi_indicator
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:39.322672+00:00
-- url     : https://prove2.me/theorems/4c6fe861-3908-45ec-9c28-4b081430108d
-- title:
--   p.17 — a wrong greedy choice in shell $B_i$ needs an error $>2^{i-1}a_n$ at $\pi^*(s)$ or $\hat\pi(s)$, with $0<\Delta(s)\le2^{i+1}a_n$
-- statement:
--   Consider a discounted MDP on a measurable state space $\mathcal S$ with a finite nonempty action set $\mathcal A$, Markov transition and reward kernels and $0<\gamma<1$, with optimal $Q$-function $Q^*$ and margin $\Delta$. Let $f:\mathcal S\times\mathcal A\to\mathbb R$ be any function, $\hat\pi$ greedy for $f$ and $\pi^*$ greedy for $Q^*$. Write $g(s)=Q^*(s,\pi^*(s))-Q^*(s,\hat\pi(s))$, $e_1(s)=Q^*(s,\pi^*(s))-f(s,\pi^*(s))$ and $e_2(s)=f(s,\hat\pi(s))-Q^*(s,\hat\pi(s))$. For every $i\ge1$, every $a_n\in\mathbb R$ and every state $s$, with $B_i=\{2^ia_n<g\le2^{i+1}a_n\}$,
--   $$\begin{aligned}\mathbb I\{B_i\}(s)&=\mathbb I\{f(s,\hat\pi(s))\ge f(s,\pi^*(s)),\ 2^ia_n<g(s)\le2^{i+1}a_n\}\\&\le\mathbb I\{e_1(s)+e_2(s)-2^ia_n>0,\ 0<g(s)\le2^{i+1}a_n\}\\&\le\mathbb I\{e_1(s)>2^{i-1}a_n,\ 0<g(s)\le2^{i+1}a_n\}+\mathbb I\{e_2(s)>2^{i-1}a_n,\ 0<g(s)\le2^{i+1}a_n\}\\&\le\mathbb I\{e_1(s)>2^{i-1}a_n,\ 0<\Delta(s)\le2^{i+1}a_n\}+\mathbb I\{e_2(s)>2^{i-1}a_n,\ 0<\Delta(s)\le2^{i+1}a_n\}.\end{aligned}$$
--
--   This is the deterministic core of the argument: if the greedy choice of $\hat\pi$ loses more than $2^ia_n$ in $Q^*$, then $f$ must be off by more than $2^{i-1}a_n$ at one of the two actions involved, and the state has a positive margin of at most $2^{i+1}a_n$.
--
--   Differences from the source:
--   - generalization: the data-driven estimate $\hat f$ for a fixed dataset, $a_n>0$, and deterministic policies $\hat\pi$, $\pi^*$ → any function $f$, any real $a_n$, and any (not necessarily measurable) greedy selections; reason: the inequality is pointwise algebra, and the source's $\hat f$, $a_n$, $\hat\pi$, $\pi^*$ are instances.
--   - encoding: policies $\pi(a\mid s)$, $\max_\pi$ and a finite action space → Markov kernels, suprema over them, and a finite nonempty type with measurable singletons; reason: Lean convention for the source's stationary stochastic policies; the maxima are attained, so the suprema are the same numbers, an MDP has at least one action, and a finite action space carries the discrete $\sigma$-algebra.
-- source:
--   Hu, Kallus, Uehara, Fast Rates for the Regret of Offline Reinforcement Learning, arXiv:2102.00479v2, §7.1, p.17 (indicator chain after "Second, for i ≥ 1")

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_MDP
import Definitions.Def_OfflineRLFastRates_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OfflineRLFastRates

open OffPolicyDRL.CrossFit

/-- The indicator chain for `Bᵢ` (Hu, Kallus, Uehara, Fast Rates for the Regret of Offline
Reinforcement Learning, arXiv:2102.00479v2, §7.1, p.17, "Second, for `i ≥ 1`").

Let `f` be any function on `S × A`, `π̂` greedy for `f` and `π*` greedy for `Q*`. Write
`g(s) = Q*(s, π*(s)) − Q*(s, π̂(s))`, `e₁(s) = Q*(s, π*(s)) − f(s, π*(s))` and
`e₂(s) = f(s, π̂(s)) − Q*(s, π̂(s))`. For every `i ≥ 1`, every `aₙ` and every state `s`,
`I{Bᵢ}(s) = I{f(s, π̂(s)) ≥ f(s, π*(s)), 2^i aₙ < g(s) ≤ 2^{i+1}aₙ}
  ≤ I{e₁(s) + e₂(s) − 2^i aₙ > 0, 0 < g(s) ≤ 2^{i+1}aₙ}
  ≤ I{e₁(s) > 2^{i−1}aₙ, 0 < g(s) ≤ 2^{i+1}aₙ} + I{e₂(s) > 2^{i−1}aₙ, 0 < g(s) ≤ 2^{i+1}aₙ}
  ≤ I{e₁(s) > 2^{i−1}aₙ, 0 < Δ(s) ≤ 2^{i+1}aₙ} + I{e₂(s) > 2^{i−1}aₙ, 0 < Δ(s) ≤ 2^{i+1}aₙ}`,
where `Bᵢ = {2^i aₙ < g ≤ 2^{i+1} aₙ}` and `Δ` is the margin of `Q*`.

**Formalization Note** The chain is deterministic (no probability), and `f` plays the role of the
estimate `f̂` for one dataset. `I` is the indicator at the fixed state `s`, in `ℝ`. -/
theorem bi_indicator {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [Fintype A] [Nonempty A] [MeasurableSingletonClass A]
    (M : MDP S A) [IsMarkovKernel M.P] [IsMarkovKernel M.Rw]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (f : S × A → ℝ) (πhat : S → A) (hf : IsGreedy f πhat)
    (πs : S → A) (hgreedy : IsGreedy (QStar M γ) πs)
    (aₙ : ℝ) (i : ℕ) (hi : 1 ≤ i) (s : S) :
    let I : Set S → ℝ := fun E => E.indicator (fun _ => (1 : ℝ)) s
    let g : S → ℝ := gapFun (QStar M γ) πs πhat
    let e₁ : S → ℝ := fun s => QStar M γ (s, πs s) - f (s, πs s)
    let e₂ : S → ℝ := fun s => f (s, πhat s) - QStar M γ (s, πhat s)
    let hi₁ : ℝ := 2 ^ (i + 1) * aₙ
    let lo : ℝ := 2 ^ (i - 1) * aₙ
    I (peelEvent g aₙ i) =
        I {s | f (s, πs s) ≤ f (s, πhat s) ∧ 2 ^ i * aₙ < g s ∧ g s ≤ hi₁} ∧
    I {s | f (s, πs s) ≤ f (s, πhat s) ∧ 2 ^ i * aₙ < g s ∧ g s ≤ hi₁} ≤
        I {s | 0 < e₁ s + e₂ s - 2 ^ i * aₙ ∧ 0 < g s ∧ g s ≤ hi₁} ∧
    I {s | 0 < e₁ s + e₂ s - 2 ^ i * aₙ ∧ 0 < g s ∧ g s ≤ hi₁} ≤
        I {s | lo < e₁ s ∧ 0 < g s ∧ g s ≤ hi₁} + I {s | lo < e₂ s ∧ 0 < g s ∧ g s ≤ hi₁} ∧
    I {s | lo < e₁ s ∧ 0 < g s ∧ g s ≤ hi₁} + I {s | lo < e₂ s ∧ 0 < g s ∧ g s ≤ hi₁} ≤
        I {s | lo < e₁ s ∧ 0 < margin (QStar M γ) s ∧ margin (QStar M γ) s ≤ hi₁} +
          I {s | lo < e₂ s ∧ 0 < margin (QStar M γ) s ∧ margin (QStar M γ) s ≤ hi₁} := by sorry

end OfflineRLFastRates
