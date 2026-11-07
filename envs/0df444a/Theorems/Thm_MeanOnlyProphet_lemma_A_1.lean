-- Prove2me | Theorems.Thm_MeanOnlyProphet_lemma_A_1
-- name    : MeanOnlyProphet.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:27:48.262118+00:00
-- url     : https://prove2.me/theorems/bc7127aa-c051-4f3c-b007-ece73f92a7c0
-- title:
--   Lemma A.1 — one-step recursion $V_t(y,x,q)\ge R_q+\phi_j V_{t+\Delta}(y_j,x_j)$
-- statement:
--   Standing context (§3.3, p.10, and App. A.1, pp.24–25): the drop rate $b$ is the step function of $N$ positive nondecreasing slopes $b_1\le\dots\le b_N$, $\theta(t)=\int_t^1b$ with $\theta(0)\le1$, $c=\max_{0\le s\le1}\{b(s)+\theta(s)\}-1>0$, $N_t$ is a multiple of $N$, $t=k/N_t$ with $k<N_t$, $\Delta=1/N_t$, $0\le x<y\le1$, and $q$ is bounded, nonnegative and nondecreasing on each $[k'/N_t,(k'+1)/N_t)$.
--
--   Let $0=r_0<r_1<\dots<r_{N_q}=\infty$ and $j\in\{1,\dots,N_q\}$. If the mean of $q$ on the step lies in $[r_{j-1},r_j]$, i.e. $\frac1\Delta\int_t^{t+\Delta}q(s)\,ds\in[r_{j-1},r_j]$, then
--   $$
--   V_t(y,x,q)\ \ge\ R_q+\phi_j\cdot V_{t+\Delta}(y_j,x_j).
--   $$
--   This is the dynamic-programming step that reduces the infimum over all rates to finitely many rate intervals, which the certificate of §3.3 evaluates layer by layer.
--
--   Differences from the source:
--   - encoding: 0 = r_0 < r_1 < ⋯ < r_{N_q} = ∞ and mean ∈ [r_{j−1}, r_j] → r : ℕ → ℝ with r 0 = 0, strictly increasing on indices < N_q, lower bound r (j−1) ≤ mean, upper bound mean ≤ r j only when j < N_q; reason: r_{N_q} = ∞ imposes no upper bound
--   - encoding: c = max_{0≤s≤1}{b(s) + θ(s)} − 1 → a parameter c with IsGreatest {b(s) + θ(s) : s ∈ [0,1]} (c + 1); reason: the maximum exists for the step drop rate; IsGreatest states it is attained and equals c + 1
--   - encoding: b > 0, the constant drop rate on [t, t + ∆] → b t, the step drop rate at t; reason: the step function is constant on [t, t + ∆) since N divides N_t
--   - encoding: (1/∆) ∫_t^{t+∆} q → N_t · ∫_t^{t+∆} q; reason: ∆ = 1/N_t
--   - encoding: q allowed in the definition of V_t → IsVtAdmissible N_t q, with the conditions imposed on all of [0,1]; reason: V_t(y, x, q) reads q only on [t, 1], and a rate on [t, 1] extends by 0 to [0, t) within the class
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), Lemma A.1, p.25 (PDF p.26)

import Mathlib
import Definitions.Def_MeanOnlyProphet_Rq

namespace MeanOnlyProphet

/-- **Lemma A.1.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…),
Lemma A.1, p.25 (PDF p.26): "For every q allowed in the definition of Vt with (1/∆) ∫_t^{t+∆} q(s) ds ∈
[rj−1 , rj ], we have Vt (y, x, q) ≥ Rq + ϕj · Vt+∆ (yj , xj )."

Standing context (§3.3, p.10; App. A.1, pp.24–25): the drop rate `b` is the step function of `N`
positive nondecreasing slopes `bs`, `θ = ∫_t^1 b` with `θ(0) ≤ 1` (§2, p.5); `c = max_{[0,1]}(b + θ) − 1 > 0`; `N_t` is divisible by
`N`, `t = t_k = k/N_t` with `k < N_t`, `∆ = 1/N_t`; `0 ≤ x < y ≤ 1`; the rate partition is
`0 = r_0 < r_1 < ⋯ < r_{N_q} = ∞` and `j ∈ [N_q]`.

**Formalization Note.** The finite partition points are `r 0, …, r (Nq − 1)` (strictly increasing,
`r 0 = 0`); `r_{N_q} = ∞` is encoded by imposing the upper bound `mean ≤ r j` only when `j < Nq`. The
constant `c` is pinned by `IsGreatest` (the maximum is attained). The constant drop rate on `[t, t+∆]`
is `b t`. The mean `(1/∆) ∫_t^{t+∆} q` is written `N_t · ∫_t^{t+∆} q`. `j - 1` is natural subtraction
with `1 ≤ j`. -/
theorem lemma_A_1 {N : ℕ} [NeZero N] (bs : Fin N → ℝ) (hbs : ∀ i, 0 < bs i) (hbm : Monotone bs)
    (hθ0 : thetaOf (stepRate bs) 0 ≤ 1) (Nt : ℕ) (hNt : 0 < Nt) (hdiv : N ∣ Nt) (c : ℝ)
    (hc : IsGreatest ((fun s => stepRate bs s + thetaOf (stepRate bs) s) '' Set.Icc 0 1) (c + 1))
    (hc0 : 0 < c) (k : ℕ) (hk : k < Nt) (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ 1)
    (Nq : ℕ) (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : StrictMonoOn r (Set.Iio Nq))
    (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ Nq) (q : ℝ → ℝ) (hq : IsVtAdmissible Nt q)
    (hlo : r (j - 1) ≤ (Nt : ℝ) * ∫ s in ((k : ℝ) / Nt)..((k : ℝ) / Nt + 1 / (Nt : ℝ)), q s)
    (hhi : j < Nq →
      (Nt : ℝ) * ∫ s in ((k : ℝ) / Nt)..((k : ℝ) / Nt + 1 / (Nt : ℝ)), q s ≤ r j) :
    Rq (stepRate bs) c ((k : ℝ) / Nt) (1 / (Nt : ℝ)) y x q
        + phiJ ((k : ℝ) / Nt) (1 / (Nt : ℝ)) y (r (j - 1)) *
          Vinf (stepRate bs) c Nt ((k : ℝ) / Nt + 1 / (Nt : ℝ))
            (yJ ((k : ℝ) / Nt) (1 / (Nt : ℝ)) y (r (j - 1)))
            (xJ (stepRate bs) c ((k : ℝ) / Nt) (1 / (Nt : ℝ)) y x (r (j - 1)))
      ≤ Vq (stepRate bs) c ((k : ℝ) / Nt) y x q := by sorry

end MeanOnlyProphet
