-- Prove2me | Theorems.Thm_HighDimStat_TailBounds_martingale_bernstein_bound_nonneg
-- name    : HighDimStat.TailBounds.martingale_bernstein_bound_nonneg
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-02T16:32:11.006834+00:00
-- url     : https://prove2.me/theorems/af3dca3f-9783-4f26-8b8c-91f90a86d568
-- title:
--   Theorem 2.19 — Martingale Bernstein bound with nonnegative scales
-- statement:
--   **Theorem 2.19 (Martingale Bernstein bound, corrected scales).** Let $(D_k,\mathcal F_k)_{k=1}^n$ be an integrable real martingale difference sequence. Let $\nu_k\in\mathbb R$ and $\alpha_k\ge0$. For every $\lambda$ with $|\lambda|<1/\alpha_k$, assume the exponential moment is integrable and
--   $$\mathbb E[e^{\lambda D_k}\mid\mathcal F_{k-1}]\le e^{\lambda^2\nu_k^2/2}\quad\text{almost surely}.$$
--   When $\alpha_k=0$, this hypothesis is required for every real $\lambda$.
--
--   Write $S_n=\sum_{k=1}^n D_k$, $V=\sum_{k=1}^n\nu_k^2$, and $A=\max_{1\le k\le n}\alpha_k$. Then $S_n$ is sub-exponential with parameters $(\sqrt V,A)$, and for all $t\ge0$,
--   $$\mathbb P(|S_n|\ge t)\le\begin{cases}2e^{-t^2/(2V)}&t\le V/A,\\2e^{-t/(2A)}&t>V/A.\end{cases}$$
--   The displayed real formulas use Lean's total division when a denominator is zero; these cases are retained in the theorem and its proof.
--
--   **Correction.** This replaces the false formal statement [85ba0a1c-b9d5-4f2d-8336-71ab5b647456](https://prove2.me/theorems/85ba0a1c-b9d5-4f2d-8336-71ab5b647456) by adding only the missing assumptions $\alpha_k\ge0$ for $1\le k\le n$. The accepted counterexample to that statement exploited a negative scale, making its moment hypothesis vacuous. All original integrability, centering, conditional moment assumptions, and both conclusions are preserved. Negative $\nu_k$ cause no issue because they enter only through their squares.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 35 (PDF p. 55), Theorem 2.19, Eq. (2.28); correction of Prove2Me theorem 85ba0a1c-b9d5-4f2d-8336-71ab5b647456 adding the missing nonnegative-scale assumption.

import Mathlib
import Definitions.Def_HighDimStat_TailBounds_IsSubExponential

open MeasureTheory

namespace HighDimStat.TailBounds

/-- **Theorem 2.19** (Martingale Bernstein bound), Wainwright, *High-Dimensional Statistics*
(2019), p. 35. Let `{(Dk,Fk)}` be a martingale difference sequence (realized as: `D k` is
`ℱ k`-measurable and `E[D k | ℱ (k-1)] = 0`, for `k = 1,...,n`), and suppose
`E[e^{λDk} | ℱ(k-1)] ≤ e^{λ²νk²/2}` a.s. for `|λ| < 1/αk`. Then (a) `∑Dk` is sub-exponential with
parameters `(√(∑νk²), max αk)`, and (b) `∑Dk` satisfies the two-regime concentration inequality
of Eq. (2.28). Explicit `Integrable` hypotheses on each `D k` and on each conditional-MGF
exponential are required to block Mathlib's `condExp`/Bochner-integral junk value `0` on a
non-integrable argument, which would otherwise let `h_cent`/`h_subexp` hold vacuously for a
non-integrable `D k` (e.g. Cauchy-distributed) regardless of the true martingale-difference or
sub-exponential-MGF property — the same guard `IsSubExponential`'s own definition already uses,
applied here to the conditional form. The scale assumptions `0 ≤ α k` are explicit: without them the conditional moment hypothesis can become vacuous. -/
theorem martingale_bernstein_bound_nonneg {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ℕ → Ω → ℝ} {ν α : ℕ → ℝ} {ℱ : Filtration ℕ mΩ}
    (n : ℕ) (hn : 1 ≤ n)
    (h_alpha : ∀ k ∈ Finset.Icc 1 n, 0 ≤ α k)
    (h_meas : ∀ k ∈ Finset.Icc 1 n, Measurable[ℱ k] (D k))
    (h_int : ∀ k ∈ Finset.Icc 1 n, Integrable (D k) μ)
    (h_cent : ∀ k ∈ Finset.Icc 1 n, μ[D k | ℱ (k - 1)] =ᵐ[μ] 0)
    (h_subexp_int : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ, (α k = 0 ∨ |lam| < 1 / α k) →
      Integrable (fun ω => Real.exp (lam * D k ω)) μ)
    (h_subexp : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ, (α k = 0 ∨ |lam| < 1 / α k) →
      (μ[fun ω => Real.exp (lam * D k ω) | ℱ (k - 1)]) ≤ᵐ[μ]
        fun _ => Real.exp (lam ^ 2 * (ν k) ^ 2 / 2)) :
    IsSubExponential (fun ω => ∑ k ∈ Finset.Icc 1 n, D k ω) μ
        (Real.sqrt (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2))
        (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α)
    ∧
    ∀ t : ℝ, 0 ≤ t →
      μ.real {ω | t ≤ |∑ k ∈ Finset.Icc 1 n, D k ω|} ≤
        if t ≤ (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2) / (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α)
        then 2 * Real.exp (-(t ^ 2) / (2 * ∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2))
        else 2 * Real.exp (-t / (2 * Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α)) := by sorry

end HighDimStat.TailBounds
