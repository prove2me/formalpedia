-- Prove2me | Theorems.Thm_MaxObjBandit_eq_103
-- name    : MaxObjBandit.eq_103
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:48.829047+00:00
-- url     : https://prove2.me/theorems/de084014-7995-482b-b69f-8358a06ad49b
-- title:
--   Eq. (103) — $\mathbb E(\Delta)\le 2(40K)^{1/3}/T^{1/3}$
-- statement:
--   Let an arm have reward law $\nu$ on $[0,1]$ with mean $\mu$, and let $U_1,U_2,\dots$ be i.i.d. rewards with law $\nu$. Let $1\le K<T$, $\tau=\lceil T^{2/3}/K^{2/3}\rceil$, and let $\Delta$ be the index deficit
--   $$
--   \Delta=\Big(\mu-\min_{n\le\tau}\Big(\bar\mu_n+\sqrt{\frac4n\log\Big(\frac{T}{Kn^{3/2}}\Big)}\;\mathbb 1_{\{n<\tau\}}\Big)\Big)^+ .
--   $$
--   Then
--   $$
--   \mathbb E(\Delta)\le\frac{2(40K)^{1/3}}{T^{1/3}} .
--   $$
--
--   Applied to arm 1, this gives the instance-independent bound (104) on the regret from committing to a suboptimal arm.
--
--   **Formalization Note** $\Delta$ takes values in $[0,\mu]$ almost surely, so its expectation is finite.
--
--   Differences from the source:
--   - encoding: the statement for arm 1 (resp. arm $i$) of a bandit instance $\boldsymbol\nu\in\mathcal V$, $K<T$ → one arm with reward law $\nu$ on $[0,1]$ and i.i.d. rewards $U_n\sim\nu$ (0-indexed), with $1\le K<T$; reason: the quantity depends only on that arm's rewards, and every such arm is an arm of some instance in $\mathcal V$
-- source:
--   Ozbay, Kamble, Maximal Objectives in the Multi-armed Bandit with Applications, arXiv:2006.06853v6, Appendix C.1, Eq. (103), p.76

import Mathlib
import Definitions.Def_MaxObjBandit_ucbIndex

open MeasureTheory ProbabilityTheory

namespace MaxObjBandit

/-- **Eq. (103)** (arXiv:2006.06853v6, Appendix C.1, Eq. (103), p.76). Let an arm have reward law `ν`
on `[0,1]` with mean `µ`, and i.i.d. rewards `U₁, U₂, …` with law `ν`. Let `1 ≤ K < T`,
`τ = ⌈T^{2/3}/K^{2/3}⌉`, and
`∆ = (µ − min_{n≤τ} (µ̄ₙ + √((4/n) log(T/(K n^{3/2}))) 𝟙{n<τ}))⁺`. Then
`E(∆) ≤ 2(40K)^{1/3}/T^{1/3}`.

**Formalization Note** As in Eq. (85), stated for one arm (the paper's arm 1); `U n` is the paper's
`U_{n+1}`. `∆` takes values in `[0, µ]` almost surely and is measurable, so its expectation is
finite. -/
theorem eq_103 {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Set.Icc 0 1) = 1)
    {U : ℕ → Ω → ℝ} (hU_meas : ∀ n, Measurable (U n)) (hU_indep : iIndepFun U P)
    (hU_law : ∀ n, P.map (U n) = ν)
    {K T : ℕ} (hK : 0 < K) (hKT : K < T) :
    ∫ ω, indexDeficit K T (∫ y, y ∂ν) (fun n => U n ω) ∂P
      ≤ 2 * (40 * (K : ℝ)) ^ ((1 : ℝ) / 3) / (T : ℝ) ^ ((1 : ℝ) / 3) := by sorry

end MaxObjBandit
