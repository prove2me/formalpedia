-- Prove2me | Theorems.Thm_MaxObjBandit_eq_89
-- name    : MaxObjBandit.eq_89
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:31.159913+00:00
-- url     : https://prove2.me/theorems/9f5234b7-4745-43b3-9087-ace20c7c2185
-- title:
--   Eq. (89) — expected number of optimistic indices of a suboptimal arm
-- statement:
--   Let an arm have reward law $\nu$ on $[0,1]$ with mean $\mu$, and let $U_1,U_2,\dots$ be i.i.d. rewards with law $\nu$. Let $1\le K<T$, $\tau=\lceil T^{2/3}/K^{2/3}\rceil$ and $0<\Delta\le1$, and count the pulls $n\le\tau$ at which the arm's upper confidence index exceeds $\mu+\Delta/2$:
--   $$
--   \eta=\sum_{n=1}^{\tau}\mathbb 1\Big\{\bar\mu_n+\sqrt{\frac4n\log\Big(\frac{T}{Kn^{3/2}}\Big)}\;\mathbb 1_{\{n<\tau\}}\ge\mu+\frac\Delta2\Big\}.
--   $$
--   Then
--   $$
--   \mathbb E(\eta)\le\frac{11}{\Delta^2}+\frac{16}{\Delta^2}\log^+\Big(\frac{T\Delta^3}{K}\Big)+\frac{24}{\Delta^2}\sqrt{\log^+\Big(\frac{T\Delta^3}{K}\Big)} .
--   $$
--
--   In the proof of Theorem 4 this is applied to a suboptimal arm $i$ with $\mu=\mu_i$ and $\Delta=\Delta_i=\mu_1-\mu_i$; it bounds the number of exploration pulls of arm $i$ while arm 1's index stays within $\Delta_i/2$ of its mean, and gives the first sum of Theorem 4.
--
--   Differences from the source:
--   - generalization: the gap $\Delta_i=\mu_1-\mu_i$ of a suboptimal arm, with $0<\Delta_i\le1$ → any $\Delta\in(0,1]$; reason: every gap $\Delta_i$ of Theorem 4's clause (i) lies in $(0,1]$, so the statement specializes to the source's; the proof on p.74 uses only $\Delta_i\le1$
--   - encoding: the statement for arm 1 (resp. arm $i$) of a bandit instance $\boldsymbol\nu\in\mathcal V$, $K<T$ → one arm with reward law $\nu$ on $[0,1]$ and i.i.d. rewards $U_n\sim\nu$ (0-indexed), with $1\le K<T$; reason: the quantity depends only on that arm's rewards, and every such arm is an arm of some instance in $\mathcal V$
-- source:
--   Ozbay, Kamble, Maximal Objectives in the Multi-armed Bandit with Applications, arXiv:2006.06853v6, Appendix C.1, pp.73–74, Eq. (89), p.74

import Mathlib
import Definitions.Def_MaxObjBandit_ucbIndex

open MeasureTheory ProbabilityTheory

namespace MaxObjBandit

/-- **Eq. (89)** (arXiv:2006.06853v6, Appendix C.1, pp.73–74, Eq. (89), p.74). Let an arm have reward
law `ν` on `[0,1]` with mean `µ`, and i.i.d. rewards `U₁, U₂, …` with law `ν`. Let `1 ≤ K < T`,
`τ = ⌈T^{2/3}/K^{2/3}⌉`, `∆ ∈ (0,1]`, and
`η = ∑_{n=1}^{τ} 𝟙{µ̄ₙ + √((4/n) log(T/(K n^{3/2}))) 𝟙{n<τ} ≥ µ + ∆/2}`. Then
`E(η) ≤ 11/∆² + (16/∆²) log⁺(T∆³/K) + (24/∆²) √(log⁺(T∆³/K))`.

**Formalization Note** The paper applies this to a suboptimal arm `i` with `µ = µᵢ` and
`∆ = ∆ᵢ = µ₁ − µᵢ ∈ (0,1]`; here `∆` is any number in `(0,1]` (its proof uses only `∆ ≤ 1`). The
sequence is `0`-indexed (`U n` is the paper's `U_{n+1}`); `ucbIndex K T U n` is the index of the page
(for `n ≤ τ` the frozen mean is the plain mean of `n` rewards). -/
theorem eq_89 {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Set.Icc 0 1) = 1)
    {U : ℕ → Ω → ℝ} (hU_meas : ∀ n, Measurable (U n)) (hU_indep : iIndepFun U P)
    (hU_law : ∀ n, P.map (U n) = ν)
    {K T : ℕ} (hK : 0 < K) (hKT : K < T) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) :
    ∫ ω, (∑ n ∈ Finset.Icc 1 (tau K T),
        if (∫ y, y ∂ν) + Δ / 2 ≤ ucbIndex K T (fun m => U m ω) n then (1 : ℝ) else 0) ∂P
      ≤ 11 / Δ ^ 2 + 16 / Δ ^ 2 * logPlus ((T : ℝ) * Δ ^ 3 / K)
        + 24 / Δ ^ 2 * Real.sqrt (logPlus ((T : ℝ) * Δ ^ 3 / K)) := by sorry

end MaxObjBandit
