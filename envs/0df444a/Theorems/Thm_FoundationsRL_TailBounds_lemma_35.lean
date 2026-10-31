-- Prove2me | Theorems.Thm_FoundationsRL_TailBounds_lemma_35
-- name    : FoundationsRL.TailBounds.lemma_35
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:24.019986+00:00
-- url     : https://prove2.me/theorems/b533020d-62e3-43bc-9bbd-f9c8f00e3ea3
-- title:
--   Lemma 35 — Freedman's inequality, uniformly over prefixes
-- statement:
--   Let $(X_t)_{t\le T}$ be a real martingale difference sequence adapted to a filtration $(\mathcal F_t)_{t\le T}$, that is, $X_t$ is $\mathcal F_t$-measurable and $\mathbb E_{t-1}[X_t]=0$ almost surely, where $\mathbb E_{t-1}[\cdot]=\mathbb E[\cdot\mid\mathcal F_{t-1}]$. Suppose $|X_t|\le R$ almost surely. Then for every $\eta\in(0,1/R)$ and every $\delta>0$, with probability at least $1-\delta$, simultaneously for all $T'\le T$,
--   $$
--   \sum_{t=1}^{T'}X_t\le\eta\sum_{t=1}^{T'}\mathbb E_{t-1}\big[X_t^2\big]+\frac{\log(\delta^{-1})}{\eta}.
--   $$
--
--   This is the martingale analogue of Bernstein's inequality: the deviation is controlled by the conditional variances instead of the worst-case range. It yields multiplicative bounds such as Lemma 36.
--
--   **Formalization Note** Conditional expectations are Mathlib's `condExp` given $\mathcal F_{t-1}$; bounded and measurable, $X_t$ and $X_t^2$ are integrable, so these are genuine conditional expectations. $R>0$ follows from $0<\eta<1/R$. $T'=0$ is included.
--
--   Differences from the source:
--   - encoding: a filtration (F_t)_{t≤T} and an adapted sequence (X_t)_{t≤T} → a filtration indexed by ℕ, with X_t F_t-measurable for 1 ≤ t ≤ T and F_0 = ℱ 0; reason: a finite filtration extends by F_t = F_T for t > T, and values of X outside 1..T do not enter; same instances
--   - encoding: a martingale difference sequence → X_t F_t-measurable and E[X_t | F_{t−1}] = 0 almost surely, for 1 ≤ t ≤ T; reason: integrability of X_t follows from |X_t| ≤ R; same instances
--   - encoding: δ ∈ (0, 1), implicit → δ > 0; reason: for δ ≥ 1 the probability bound 1 − δ ≤ 0 is trivial; only δ ≤ 0, where log(δ⁻¹) is undefined, is excluded
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 35, p. 157

import Mathlib
open MeasureTheory ProbabilityTheory

namespace FoundationsRL.TailBounds

/-- **Lemma 35** (Freedman's inequality, Bernstein for martingales). Let `(X_t)_{t ≤ T}` be a
real-valued martingale difference sequence adapted to a filtration `(F_t)_{t ≤ T}`. If `|X_t| ≤ R`
almost surely, then for any `η ∈ (0, 1/R)`, with probability at least `1 − δ`, for all `T′ ≤ T`,
`∑_{t=1}^{T′} X_t ≤ η ∑_{t=1}^{T′} E_{t−1}[X_t²] + log(δ⁻¹)/η`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Lemma 35, p. 157.

**Formalization Note.** `E_{t−1}[·]` is the conditional expectation `μ[· | ℱ (t − 1)]` given
`F_{t−1}`. Martingale difference: `X_t` is `F_t`-measurable and `E_{t−1}[X_t] = 0` a.s., for
`1 ≤ t ≤ T`; bounded and measurable, `X_t` and `X_t²` are integrable, so the conditional
expectations are genuine. `R > 0` is implied by `0 < η < 1/R`. `T′ = 0` is included. -/
theorem lemma_35 {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (T : ℕ) (X : ℕ → Ω → ℝ)
    (hX : ∀ t ∈ Finset.Icc 1 T, StronglyMeasurable[ℱ t] (X t))
    (hmds : ∀ t ∈ Finset.Icc 1 T, μ[X t | ℱ (t - 1)] =ᵐ[μ] 0)
    (R : ℝ) (hbdd : ∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂μ, |X t ω| ≤ R)
    (η : ℝ) (hη0 : 0 < η) (hηR : η < 1 / R)
    (δ : ℝ) (hδ : 0 < δ) :
    1 - δ ≤ μ.real {ω | ∀ T' ≤ T,
        ∑ t ∈ Finset.Icc 1 T', X t ω ≤
          η * ∑ t ∈ Finset.Icc 1 T', (μ[fun ω' => X t ω' ^ 2 | ℱ (t - 1)]) ω
            + Real.log δ⁻¹ / η} := by sorry

end FoundationsRL.TailBounds
