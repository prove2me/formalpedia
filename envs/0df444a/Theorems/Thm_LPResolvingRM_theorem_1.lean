-- Prove2me | Theorems.Thm_LPResolvingRM_theorem_1
-- name    : LPResolvingRM.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:39:21.081787+00:00
-- url     : https://prove2.me/theorems/d8cf1bb0-dd6d-4aea-8ce8-39d5eccb1fe5
-- title:
--   Theorem 1 — Hoeffding's inequality for dependent data (van de Geer 2002)
-- statement:
--   Let $X_1,\dots,X_T$ be integrable random variables adapted to a filtration $(\mathcal F_t)$ with $\mathcal F_0$ trivial and $\mathbb E[X_t|\mathcal F_{t-1}]=0$ for $t=1,\dots,T$. Suppose $L_t,U_t$ are $\mathcal F_{t-1}$-measurable with $L_t\le X_t\le U_t$ almost surely. Let $S_t=\sum_{s=1}^tX_s$ and $V_t=\sum_{s=1}^t(U_s-L_s)^2$. Then for any $b>0$, $c>0$ and $T\in\mathbb N_+$,
--   $$\mathbb P\big(|S_t|\ge b,\ V_t\le c^2\text{ for some }t\in\{1,\dots,T\}\big)\le2e^{-2b^2/c^2}.$$
--
--   This maximal inequality with predictable ranges controls the martingale part of the constraint process in Lemma 12.
--
--   Differences from the source:
--   - encoding: S_t = ∑_{s=1}^t X_t → S_t = ∑_{s=1}^t X_s; reason: typo
--   - encoding: F₀ = ∅ → ℱ 0 = ⊥ (the trivial σ-algebra); reason: the intended trivial σ-algebra
--   - encoding: E[X_t | F_{t−1}] (integrability implicit) → X_t integrable; reason: the conditional expectation presupposes it
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Theorem 1, p.14 (van de Geer 2002)

import Mathlib

open MeasureTheory

namespace LPResolvingRM

/-- **Theorem 1 (Hoeffding's inequality for dependent data, van de Geer 2002)**
(arXiv:2101.11092v3, p.14): let `X_1, …, X_T` be adapted to the filtration `(ℱ_t)` with
`E[X_t | ℱ_{t−1}] = 0` for `t = 1, …, T`, where `ℱ_0` is trivial. Suppose `L_t, U_t` are
`ℱ_{t−1}`-measurable with `L_t ≤ X_t ≤ U_t` almost surely. Let `S_t = ∑_{s=1}^t X_s` and
`V_t = ∑_{s=1}^t (U_s − L_s)²`. Then for any `b > 0`, `c > 0` and `T ∈ ℕ₊`,

`P(|S_t| ≥ b, V_t ≤ c² for some t ∈ {1, …, T}) ≤ 2 e^{−2b²/c²}`.

**Formalization Note.** "`ℱ_0 = ∅`" is the trivial σ-algebra `⊥`. The sum is over `X_s` (the
page prints `X_t`). Each `X_t` is integrable, which the conditional expectation presupposes. The
probability is `μ.real` of the event. -/
theorem theorem_1 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (hℱ0 : ℱ 0 = ⊥) (X Lo Up : ℕ → Ω → ℝ) (T : ℕ) (hT : 1 ≤ T)
    (hadapt : ∀ t ∈ Finset.Icc 1 T, StronglyMeasurable[ℱ t] (X t))
    (hint : ∀ t ∈ Finset.Icc 1 T, Integrable (X t) μ)
    (hmart : ∀ t ∈ Finset.Icc 1 T, μ[X t | ℱ (t - 1)] =ᵐ[μ] 0)
    (hLo : ∀ t ∈ Finset.Icc 1 T, StronglyMeasurable[ℱ (t - 1)] (Lo t))
    (hUp : ∀ t ∈ Finset.Icc 1 T, StronglyMeasurable[ℱ (t - 1)] (Up t))
    (hbdd : ∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂μ, Lo t ω ≤ X t ω ∧ X t ω ≤ Up t ω)
    (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    μ.real {ω | ∃ t ∈ Finset.Icc 1 T, b ≤ |∑ s ∈ Finset.Icc 1 t, X s ω| ∧
        ∑ s ∈ Finset.Icc 1 t, (Up s ω - Lo s ω) ^ 2 ≤ c ^ 2} ≤
      2 * Real.exp (-(2 * b ^ 2 / c ^ 2)) := by sorry

end LPResolvingRM
