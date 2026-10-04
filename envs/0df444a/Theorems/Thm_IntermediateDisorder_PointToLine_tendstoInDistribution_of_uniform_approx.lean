-- Prove2me | Theorems.Thm_IntermediateDisorder_PointToLine_tendstoInDistribution_of_uniform_approx
-- name    : IntermediateDisorder.PointToLine.tendstoInDistribution_of_uniform_approx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:04:22.706075+00:00
-- url     : https://prove2.me/theorems/022ed0de-3fff-492a-991a-c7666a8fa51f
-- title:
--   Lemma 4.2 — convergence in law through a uniform-in-$n$ approximation
-- statement:
--   Let $Y_k^n$, $Y_k$, $Y^n$, $Y$ ($k,n\in\mathbb N$) be real random variables such that, for each fixed $n$, the variables $Y_k^n$ ($k\in\mathbb N$) and $Y^n$ are defined on a common probability space $(\Omega_n,Q_n)$. Assume
--
--   1. $Y_k^n\xrightarrow{(d)}Y_k$ as $n\to\infty$, for every $k$;
--   2. $Y_k^n\to Y^n$ in probability as $k\to\infty$, uniformly in $n$: for every $\varepsilon>0$,
--   $$\lim_{k\to\infty}\ \sup_{n}\ Q_n\big(|Y_k^n-Y^n|>\varepsilon\big)=0;$$
--   3. $Y_k\xrightarrow{(d)}Y$ as $k\to\infty$.
--
--   Then $Y^n\xrightarrow{(d)}Y$ as $n\to\infty$.
--
--   This is the standard approximation device ([Billingsley, Convergence of Probability Measures, Ch. 1, Thm. 4.2] in the paper's citation) used to pass from finitely many chaos orders to the full series in Lemma 4.4 and Proposition 5.3.
--
--   **Formalization Note** The spaces of $Y_k^n,Y^n$ may depend on $n$, those of $Y_k$ on $k$, and $Y$ lives on its own space. "Random variable" includes measurability; for $Y^n$ this is stated as a hypothesis, for the others it is part of the convergence-in-distribution hypotheses. The uniformity is exactly the page's "in probability, uniformly in $n$", which is stronger than Billingsley's $\lim_k\limsup_n$.
-- source:
--   Alberts, Khanin, Quastel, The intermediate disorder regime for directed polymers in dimension 1+1, arXiv:1202.4398v3, p. 23, Lemma 4.2

import Mathlib

namespace IntermediateDisorder.PointToLine

open MeasureTheory ProbabilityTheory Filter Topology

/-- Lemma 4.2: if `Y_k^n → Y_k` in distribution as `n → ∞` for each `k`, `Y_k^n → Y^n` in
probability as `k → ∞` uniformly in `n` (for every `ε > 0`,
`sup_n Q_n(|Y_k^n - Y^n| > ε) → 0`), and `Y_k → Y` in distribution, then `Y^n → Y` in
distribution. For each `n`, `Y_k^n` (all `k`) and `Y^n` live on a common probability space. -/
theorem tendstoInDistribution_of_uniform_approx
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    {Ωk : ℕ → Type*} [∀ k, MeasurableSpace (Ωk k)] (Pk : ∀ k, Measure (Ωk k))
    [∀ k, IsProbabilityMeasure (Pk k)]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Ykn : ℕ → ∀ n, Ω n → ℝ) (Yk : ∀ k, Ωk k → ℝ) (Yn : ∀ n, Ω n → ℝ) (Y : Ω' → ℝ)
    (hYn : ∀ n, AEMeasurable (Yn n) (P n))
    (h_row : ∀ k, TendstoInDistribution (Ykn k) atTop (Yk k) P (Pk k))
    (h_unif : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun k => ⨆ n, P n {a | ε < |Ykn k n a - Yn n a|}) atTop (𝓝 0))
    (h_col : TendstoInDistribution Yk atTop Y Pk P') :
    TendstoInDistribution Yn atTop Y P P' := by sorry

end IntermediateDisorder.PointToLine
