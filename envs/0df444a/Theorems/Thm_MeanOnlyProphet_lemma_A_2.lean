-- Prove2me | Theorems.Thm_MeanOnlyProphet_lemma_A_2
-- name    : MeanOnlyProphet.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:28:25.753394+00:00
-- url     : https://prove2.me/theorems/1d9d7218-625b-4ed4-a67a-708787d19018
-- title:
--   Lemma A.2 — lower bounds on $R_q$
-- statement:
--   Standing context (§3.3, p.10, and App. A.1, pp.24–25): the drop rate $b$ is the step function of $N$ positive nondecreasing slopes $b_1\le\dots\le b_N$, $\theta(t)=\int_t^1b$ with $\theta(0)\le1$, $c=\max_{0\le s\le1}\{b(s)+\theta(s)\}-1>0$, $N_t$ is a multiple of $N$, $t=k/N_t$ with $k<N_t$, $\Delta=1/N_t$, $0\le x<y\le1$, and $q$ is bounded and nonnegative on $[t,t+\Delta)$ and nondecreasing there.
--
--   Suppose $\frac1\Delta\int_t^{t+\Delta}q(s)\,ds\le r<\infty$, and let
--   $$
--   \alpha=\Big(y\,b\,e^{-\Delta r}+(-p)^+\frac{I_r}{\Delta}\Big)\Delta^2,\qquad \beta=\Delta\,(u+y\,b\,I_r).
--   $$
--   Then $\alpha,\beta>0$ and
--   $$
--   R_q\ \ge\ \min\{p\Delta,\,p\,I_r\}+\max\left\{\beta-\frac{\beta^2}{4\alpha},\ \frac\alpha4\Big(3+2\log\frac\beta\alpha\Big)\right\}.
--   $$
--   Moreover, when $\beta e^{-r}>\alpha/2$,
--   $$
--   R_q\ \ge\ \min\{p\Delta,\,p\,I_r\}+\beta e^{-r}+\frac{\alpha r}{2}-\frac{\alpha^2}{24\,(\beta e^{-r}-\alpha/2)} .
--   $$
--   These bounds supply the constants $a_j$ of the one-step recursion for each finite rate interval.
--
--   Differences from the source:
--   - encoding: b > 0, the constant drop rate on [t, t + ∆] → b t, the step drop rate at t; reason: the step function is constant on [t, t + ∆) since N divides N_t
--   - encoding: c = max_{0≤s≤1}{b(s) + θ(s)} − 1 → a parameter c with IsGreatest {b(s) + θ(s) : s ∈ [0,1]} (c + 1); reason: the maximum is attained for the step drop rate
--   - encoding: (−p)^+ and r < ∞ → max (−p) 0 and r : ℝ; reason: notation
--   - encoding: (1/∆) ∫_t^{t+∆} q → N_t · ∫_t^{t+∆} q; reason: ∆ = 1/N_t
--   - encoding: a bounded nonnegative rate q that is nondecreasing on the interval [t, t + ∆] → the same conditions on the half-open [t, t + ∆); reason: q(t + ∆) affects no integral, and V_t's class uses half-open intervals
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), Lemma A.2, p.26 (PDF p.27)

import Mathlib
import Definitions.Def_MeanOnlyProphet_Rq

namespace MeanOnlyProphet

/-- **Lemma A.2.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…),
Lemma A.2, p.26 (PDF p.27): "Suppose that (1/∆) · ∫_t^{t+∆} q(s) ds ≤ r < ∞. Let α = (y · b · e^{−∆·r} +
(−p)^+ · Ir/∆) · ∆², β = ∆ · (u + y · b · Ir). We have α, β > 0 and Rq ≥ min{p · ∆, p · Ir} + max{β −
β²/(4 · α), (α/4) · (3 + 2 · log(β/α))}. Moreover, when β · e^{−r} > α/2, we also have Rq ≥ min{p · ∆,
p · Ir} + β · e^{−r} + α · r/2 − α²/(24 · (β · e^{−r} − α/2))."

Standing context as in Lemma A.1 (§3.3, p.10; App. A.1, pp.24–25): step drop rate of positive
nondecreasing slopes with `θ(0) ≤ 1` (§2, p.5), `c = max(b + θ) − 1 > 0`, `N ∣ N_t`, `t = k/N_t`,
`∆ = 1/N_t`, `0 ≤ x < y ≤ 1`, and (p.25) `q` a bounded nonnegative rate that is nondecreasing on this
time interval.

**Formalization Note.** `r` is a real number (`r < ∞`); `(−p)^+` is `max (-p) 0`; `b` is the constant
drop rate on `[t, t+∆]`, read as `b t`; the mean `(1/∆) ∫_t^{t+∆} q` is written `N_t · ∫_t^{t+∆} q`. The conditions on `q` are on the half-open
`[t, t+∆)`, as in `V_t`'s class (p.24); `q(t+∆)` affects no integral, and `q` is free outside the interval.
`β/α > 0` by the first two conclusions, so `Real.log` is the true
logarithm. -/
theorem lemma_A_2 {N : ℕ} [NeZero N] (bs : Fin N → ℝ) (hbs : ∀ i, 0 < bs i) (hbm : Monotone bs)
    (hθ0 : thetaOf (stepRate bs) 0 ≤ 1) (Nt : ℕ) (hNt : 0 < Nt) (hdiv : N ∣ Nt) (c : ℝ)
    (hc : IsGreatest ((fun s => stepRate bs s + thetaOf (stepRate bs) s) '' Set.Icc 0 1) (c + 1))
    (hc0 : 0 < c) (k : ℕ) (hk : k < Nt) (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ 1)
    (q : ℝ → ℝ) (hq0 : ∀ s ∈ Set.Ico ((k : ℝ) / Nt) ((k : ℝ) / Nt + 1 / (Nt : ℝ)), 0 ≤ q s)
    (hqb : ∃ M : ℝ, ∀ s ∈ Set.Ico ((k : ℝ) / Nt) ((k : ℝ) / Nt + 1 / (Nt : ℝ)), q s ≤ M)
    (hqm : MonotoneOn q (Set.Ico ((k : ℝ) / Nt) ((k : ℝ) / Nt + 1 / (Nt : ℝ)))) (r : ℝ)
    (hr : (Nt : ℝ) * ∫ s in ((k : ℝ) / Nt)..((k : ℝ) / Nt + 1 / (Nt : ℝ)), q s ≤ r) :
    let b := stepRate bs
    let t := (k : ℝ) / Nt
    let Δ := 1 / (Nt : ℝ)
    let p := pCoef b c t y x
    let α := (y * b t * Real.exp (-Δ * r) + max (-p) 0 * (Ir r Δ / Δ)) * Δ ^ 2
    let β := Δ * (uCoef b t y + y * b t * Ir r Δ)
    0 < α ∧ 0 < β ∧
      min (p * Δ) (p * Ir r Δ) + max (β - β ^ 2 / (4 * α)) (α / 4 * (3 + 2 * Real.log (β / α)))
        ≤ Rq b c t Δ y x q ∧
      (α / 2 < β * Real.exp (-r) →
        min (p * Δ) (p * Ir r Δ) + β * Real.exp (-r) + α * r / 2
            - α ^ 2 / (24 * (β * Real.exp (-r) - α / 2)) ≤ Rq b c t Δ y x q) := by sorry

end MeanOnlyProphet
