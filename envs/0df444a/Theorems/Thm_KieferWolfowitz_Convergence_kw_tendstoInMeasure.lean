-- Prove2me | Theorems.Thm_KieferWolfowitz_Convergence_kw_tendstoInMeasure
-- name    : KieferWolfowitz.Convergence.kw_tendstoInMeasure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:49:18.200372+00:00
-- url     : https://prove2.me/theorems/81b7a996-2533-4a16-9ad1-33179123f40d
-- title:
--   §3 Theorem (pp. 462–465, (3.22)) — the Kiefer–Wolfowitz iterates $z_n$ converge in probability to $\theta$
-- statement:
--   Let $H(\cdot\mid x)$, $x\in\mathbb R$, be a measurable family of probability distributions on $\mathbb R$ with regression function $M(x)=\int y\,dH(y\mid x)$, such that
--
--   1. each $H(\cdot\mid x)$ has a finite second moment and $\int(y-M(x))^2\,dH(y\mid x)\le S$ (2.2);
--   2. $M$ is strictly increasing for $x<\theta$ and strictly decreasing for $x>\theta$;
--   3. $M$ satisfies Conditions 1, 2 and 3 of the paper (2.8)–(2.10), for some positive constants $\beta,B,\rho,R$.
--
--   Let $a_n,c_n>0$ satisfy $c_n\to0$, $\sum a_n=\infty$, $\sum a_nc_n<\infty$, $\sum a_n^2c_n^{-2}<\infty$, let $z_1$ be any number, and let
--   $$z_{n+1}=z_n+a_n\,\frac{y_{2n}-y_{2n-1}}{c_n},$$
--   where, given the past, $y_{2n-1}$ and $y_{2n}$ are independent with laws $H(\cdot\mid z_n-c_n)$ and $H(\cdot\mid z_n+c_n)$. Then $z_n$ converges to $\theta$ in probability:
--   $$\text{for all }\eta>0,\qquad P\{|z_n-\theta|>\eta\}\longrightarrow0\quad(n\to\infty).$$
--
--   This is the theorem of the paper: by observing the regression function only through noisy evaluations at two nearby points, the scheme locates its maximizer $\theta$. $\theta$ is the maximum point of $M$ (the paper's Summary), a consequence of unimodality and the continuity at $\theta$ that Condition 1 gives; it is not assumed separately.
--
--   **Formalization Note** $H$ is a Markov kernel; Condition 1 carries the repair $x'\neq x''$; Condition 3's infimum is stated pointwise; "independent chance variables with respective distributions $H(y\mid z_n\mp c_n)$" is the conditional law given a filtration $(\mathcal F_n)$ to which the process is adapted (see the model definition). Convergence in probability is Mathlib's `TendstoInMeasure`, which uses $\ge\eta$ in place of the paper's $>\eta$; over all $\eta>0$ the two are equivalent, and both are the paper's (3.22). Indices are 0-based. No rate and no almost-sure convergence is claimed.
-- source:
--   Kiefer & Wolfowitz, Stochastic estimation of the maximum of a regression function, Ann. Math. Statist. 23 (1952), §3 Theorem: p. 462 (statement), p. 463 (§3 title), p. 465 (3.22)

import Mathlib
import Definitions.Def_KieferWolfowitz_Convergence_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace KieferWolfowitz.Convergence

/-- Kiefer & Wolfowitz (1952), §3 Theorem (p. 462; §3 title p. 463; explicit form (3.22), p. 465):
under (2.2), unimodality about `θ`, Conditions 1–3 and (2.3)–(2.6), the Kiefer–Wolfowitz iterates
`z_n` of (2.7) converge in probability to `θ`. -/
theorem kw_tendstoInMeasure {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (S θ : ℝ)
    (hS : SecondMomentBound H S) (hM : Unimodal (regFun H) θ)
    (h1 : ∃ β B : ℝ, 0 < β ∧ 0 < B ∧ Cond1 (regFun H) θ β B)
    (h2 : ∃ ρ R : ℝ, 0 < ρ ∧ 0 < R ∧ Cond2 (regFun H) ρ R)
    (h3 : Cond3 (regFun H) θ)
    (a c : ℕ → ℝ) (hac : StepSizes a c) (z₁ : ℝ)
    (z yminus yplus : ℕ → Ω → ℝ) (hz : IsKWProcess H a c z₁ P ℱ z yminus yplus) :
    TendstoInMeasure P z atTop (fun _ => θ) := by sorry

end KieferWolfowitz.Convergence
