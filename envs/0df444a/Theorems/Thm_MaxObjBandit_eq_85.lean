-- Prove2me | Theorems.Thm_MaxObjBandit_eq_85
-- name    : MaxObjBandit.eq_85
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:32.383814+00:00
-- url     : https://prove2.me/theorems/ee31b31a-22f0-46c1-b3df-f550fd30dc51
-- title:
--   Eq. (85) — tail bound $P(\Delta>x)\le\min(1,40K/(Tx^3))$ for the index deficit of arm 1
-- statement:
--   Let an arm have reward law $\nu$ on $[0,1]$ with mean $\mu$, and let $U_1,U_2,\dots$ be i.i.d. rewards with law $\nu$. Let $1\le K<T$, $\tau=\lceil T^{2/3}/K^{2/3}\rceil$, and let
--   $$
--   \Delta=\Big(\mu-\min_{n\le\tau}\Big(\bar\mu_n+\sqrt{\frac4n\log\Big(\frac{T}{Kn^{3/2}}\Big)}\;\mathbb 1_{\{n<\tau\}}\Big)\Big)^+
--   $$
--   be the index deficit, where $\bar\mu_n$ is the mean of the first $n$ rewards. Then for every $x>0$,
--   $$
--   P(\Delta>x)\le\min\Big(1,\frac{40K}{Tx^3}\Big).
--   $$
--
--   In the proof of Theorem 4 this is applied to the optimal arm 1; it bounds the probability that arm 1 looks worse than it is by more than $x$, and is used in (91), (92) and (101).
--
--   Differences from the source:
--   - encoding: for any $x\ge0$ → for $x>0$; reason: at $x=0$ the printed bound is $\min(1,\infty)=1$, which is trivial, while Lean's $40K/0=0$ would make it false
--   - encoding: the statement for arm 1 (resp. arm $i$) of a bandit instance $\boldsymbol\nu\in\mathcal V$, $K<T$ → one arm with reward law $\nu$ on $[0,1]$ and i.i.d. rewards $U_n\sim\nu$ (0-indexed), with $1\le K<T$; reason: the quantity depends only on that arm's rewards, and every such arm is an arm of some instance in $\mathcal V$
-- source:
--   Ozbay, Kamble, Maximal Objectives in the Multi-armed Bandit with Applications, arXiv:2006.06853v6, Appendix C.1, Eq. (85), p.72

import Mathlib
import Definitions.Def_MaxObjBandit_ucbIndex

open MeasureTheory ProbabilityTheory

namespace MaxObjBandit

/-- **Eq. (85)** (arXiv:2006.06853v6, Appendix C.1, Eq. (85), p.72). Let an arm have reward law `ν`
on `[0,1]` with mean `µ`, and i.i.d. rewards `U₁, U₂, …` with law `ν`. Let `1 ≤ K < T`,
`τ = ⌈T^{2/3}/K^{2/3}⌉`, and
`∆ = (µ − min_{n≤τ} (µ̄ₙ + √((4/n) log(T/(K n^{3/2}))) 𝟙{n<τ}))⁺`. Then for every `x > 0`,
`P(∆ > x) ≤ min(1, 40K/(Tx³))`.

**Formalization Note** The paper applies this to arm 1 (`µ = µ₁`); it is stated for one arm because
`∆` depends only on that arm's rewards. The sequence is `0`-indexed (`U n` is the paper's
`U_{n+1}`). The page says "for any `x ≥ 0`"; at `x = 0` the printed bound is `min(1, ∞) = 1`, which is
trivial, while Lean's `40K/0 = 0` would make it false, so `x > 0` is assumed. -/
theorem eq_85 {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Set.Icc 0 1) = 1)
    {U : ℕ → Ω → ℝ} (hU_meas : ∀ n, Measurable (U n)) (hU_indep : iIndepFun U P)
    (hU_law : ∀ n, P.map (U n) = ν)
    {K T : ℕ} (hK : 0 < K) (hKT : K < T) {x : ℝ} (hx : 0 < x) :
    P.real {ω | x < indexDeficit K T (∫ y, y ∂ν) (fun n => U n ω)}
      ≤ min 1 (40 * (K : ℝ) / ((T : ℝ) * x ^ 3)) := by sorry

end MaxObjBandit
