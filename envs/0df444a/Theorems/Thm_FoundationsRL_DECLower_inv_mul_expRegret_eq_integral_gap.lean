-- Prove2me | Theorems.Thm_FoundationsRL_DECLower_inv_mul_expRegret_eq_integral_gap
-- name    : FoundationsRL.DECLower.inv_mul_expRegret_eq_integral_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:15:31.090433+00:00
-- url     : https://prove2.me/theorems/1a8e276f-b29c-4ab3-a410-6e23e55d33ac
-- title:
--   (6.37) — $\frac1T\,\mathbb E^M[\mathrm{Reg}(T)]=\mathbb E_{\pi\sim p_M}[g^M(\pi)]$
-- statement:
--   Let $p$ be an algorithm, $M$ a model (rewards in $[0,1]$) and $T$ a horizon. Then
--
--   $$
--   \frac1T\,\mathbb E^M[\mathrm{Reg}(T)]=\mathbb E_{\pi\sim p_M}\bigl[g^M(\pi)\bigr],
--   $$
--
--   where $p_M=\mathbb E^M[\frac1T\sum_{t=1}^Tp_t]$ is the average action distribution and $g^M(\pi)=f^M(\pi_M)-f^M(\pi)$.
--
--   It turns the expected regret, a sum over rounds of history-dependent quantities, into a single expectation over decisions, which is the form the lower-bound argument compares across models.
--
--   Differences from the source:
--   - generalization: $T\in\mathbb N$, $T\ge1$ (the factor $1/T$) → every $T\in\mathbb N$; reason: at $T=0$ both sides are $0$ in Lean ($0^{-1}=0$, $p_M$ the zero measure); the notes' case is $T\ge1$
--   - reading: reward space $\mathcal R\subseteq\mathbb R$ → rewards in $[0,1]$ (a model); reason: the proof of Proposition 28 states "rewards are in $[0,1]$" (p. 109), as does its source arXiv:2301.08215
--   - generalization: $f^M(\pi_M)$ with $\pi_M=\arg\max_\pi f^M(\pi)$ → $\sup_\pi f^M(\pi)$; reason: equal whenever the argmax exists, which the notation presupposes
--   - encoding: rounds $t=1,\dots,T$ → $0$-based indices; reason: Lean convention; same instances
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, proof of Proposition 28, (6.37), p. 108

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_IsModel
import Definitions.Def_FoundationsRL_DECLower_expRegret
import Definitions.Def_FoundationsRL_DECLower_avgActionDist

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.DECLower

/-- **(6.37): expected regret through the average action distribution.**
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, proof of Proposition 28, (6.37), p. 108: "For all models M, we have
(1/T) E^M[Reg(T)] = E_{π∼p_M}[g^M(π)]."

For every algorithm, every model `M` (rewards in `[0, 1]`) and every horizon `T`,
`T⁻¹ · E_M[Reg(T)] = ∫ g^M dp_M`.

**Formalization Note.** `T = 0` is allowed (both sides are `0`: Lean's `0⁻¹ = 0` and `p_M` is the
zero measure); the paper's `T ∈ ℕ` has `T ≥ 1`. -/
theorem inv_mul_expRegret_eq_integral_gap {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (alg : Algorithm D O) (M : Kernel D (ℝ × O)) (hM : IsModel M) (T : ℕ) :
    (T : ℝ)⁻¹ * expRegret alg M T = ∫ d, gap M d ∂(avgActionDist alg M T) := by sorry

end FoundationsRL.DECLower
