-- Prove2me | Theorems.Thm_HighDimProb_RandomProcesses_slepian
-- name    : HighDimProb.RandomProcesses.slepian
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:00:55.044365+00:00
-- url     : https://prove2.me/theorems/45dcf9d6-c3eb-48d8-ad5d-5ab5e00a1f80
-- title:
--   Theorem 7.2.1 — Slepian's inequality for Gaussian processes
-- statement:
--   This is **Slepian's inequality**, the first and most classical comparison inequality for
--   Gaussian processes: it says that the faster a Gaussian process grows, in terms of the size of
--   its increments, the larger its supremum tends to be — made precise as a stochastic-domination
--   statement between the two processes' suprema.
--
--   Let $(X_t)_{t\in T}$ and $(Y_t)_{t\in T}$ be two mean zero Gaussian processes on a common
--   probability space, indexed by an arbitrary (possibly uncountable) nonempty set $T$ (a family of
--   real random variables such that every finite linear combination is Gaussian). Assume that for
--   all $t,s\in T$,
--
--   $$
--   E X_t^2 = E Y_t^2 \qquad\text{and}\qquad E(X_t - X_s)^2 \le E(Y_t - Y_s)^2.
--   $$
--
--   Then for every $\tau \in \mathbb R$,
--
--   $$
--   P\Bigl\{\sup_{t\in T} X_t \ge \tau\Bigr\} \;\le\; P\Bigl\{\sup_{t\in T} Y_t \ge \tau\Bigr\}.
--   $$
--
--   Consequently,
--
--   $$
--   E \sup_{t\in T} X_t \;\le\; E \sup_{t\in T} Y_t.
--   $$
--
--   When the tail comparison holds for every $\tau$, one says $X$ is *stochastically dominated* by
--   $Y$. The book proves this first for finite-dimensional Gaussian vectors (Theorem 7.2.9) via
--   Gaussian interpolation, and extends it to a general index set $T$ through the process's
--   finite-dimensional marginals.
--
--   **Formalization Note** `P{sup ≥ τ}` is `ProcessTailProb` and `E sup` is `ProcessESup`, both
--   defined through finite marginals of `T` in the sense of the book's own footnote 3 to this
--   section (an uncountable `T` makes the pointwise supremum non-measurable in general).
--   `IsGaussianProcess` (Mathlib) is the Gaussian-process hypothesis. Unlike Theorem 7.2.9's
--   restriction to `τ ≥ 0`, this general form holds for every real `τ`, exactly as the book states
--   it.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 156, Theorem 7.2.1

import Mathlib
import Definitions.Def_HighDimProb_RandomProcesses_ProcessESup
import Definitions.Def_HighDimProb_RandomProcesses_ProcessTailProb

open MeasureTheory ProbabilityTheory

namespace HighDimProb.RandomProcesses

/-- **Theorem 7.2.1** (Slepian's inequality), Vershynin, *High-Dimensional Probability* (2018),
p. 156 (PDF p. 164).

Let `(X_t)_{t∈T}` and `(Y_t)_{t∈T}` be two mean zero Gaussian processes on an arbitrary
(possibly uncountable) nonempty index set `T`. Assume that for all `t, s ∈ T`, `E X_t² = E Y_t²`
and `E(X_t − X_s)² ≤ E(Y_t − Y_s)²`. Then for every `τ ∈ ℝ`, `P{sup_{t∈T} X_t ≥ τ} ≤
P{sup_{t∈T} Y_t ≥ τ}`. Consequently, `E sup_{t∈T} X_t ≤ E sup_{t∈T} Y_t`. -/
theorem slepian :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {T : Type} [Nonempty T] (X Y : T → Ω → ℝ)
      (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
      (hXmean : ∀ t, ∫ ω, X t ω ∂P = 0) (hYmean : ∀ t, ∫ ω, Y t ω ∂P = 0)
      (hvar : ∀ t, ∫ ω, (X t ω) ^ 2 ∂P = ∫ ω, (Y t ω) ^ 2 ∂P)
      (hinc : ∀ t s, ∫ ω, (X t ω - X s ω) ^ 2 ∂P ≤ ∫ ω, (Y t ω - Y s ω) ^ 2 ∂P),
      (∀ τ : ℝ, processTailProb P X τ ≤ processTailProb P Y τ) ∧
      processESup P X ≤ processESup P Y := by sorry

end HighDimProb.RandomProcesses
