-- Prove2me | Theorems.Thm_HighDimStat_TailBounds_martingale_bernstein_bound_v2
-- name    : HighDimStat.TailBounds.martingale_bernstein_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:20:40.096371+00:00
-- url     : https://prove2.me/theorems/593fe499-600f-48fb-9622-8f0db8fbc889
-- title:
--   Theorem 2.19 — the martingale Bernstein bound (nonnegative scales, $1/0=+\infty$ convention)
-- statement:
--   **Theorem 2.19 (Martingale Bernstein bound).** Let $\{(D_k,\mathcal F_k)\}_{k=1}^n$ be a
--   martingale difference sequence, and suppose that for nonnegative scale parameters
--   $\alpha_k \ge 0$ and real $\nu_k$,
--   $\mathbb E[e^{\lambda D_k}\mid\mathcal F_{k-1}]\le e^{\lambda^2\nu_k^2/2}$ almost surely for
--   every $|\lambda|<1/\alpha_k$ (with $1/0 = +\infty$, so for every $\lambda\in\mathbb R$ when
--   $\alpha_k = 0$). Write $\alpha_* := \max_{k\le n}\alpha_k$ and $V := \sum_{k=1}^n \nu_k^2$. Then:
--
--   (a) The sum $\sum_{k=1}^n D_k$ is sub-exponential with parameters $(\sqrt V,\ \alpha_*)$.
--
--   (b) The sum satisfies the concentration inequality
--
--   $$
--   \mathbb P\Big[\Big|\sum_{k=1}^n D_k\Big|\ge t\Big] \le
--   \begin{cases}
--   2e^{-t^2/(2V)} & \text{if } 0\le t\le V/\alpha_*, \\
--   2e^{-t/(2\alpha_*)} & \text{if } t > V/\alpha_*,
--   \end{cases}
--   $$
--
--   where, again with $1/0=+\infty$, the first regime covers every $t \ge 0$ when $\alpha_* = 0$.
--
--   This is the chapter's general Bernstein-type bound for martingale difference sequences,
--   obtained by controlling the moment generating function of the partial sum and applying the
--   Chernoff bound; by specialization ($\alpha_k = 0$) it yields the Azuma–Hoeffding inequality
--   (Corollary 2.20) and the bounded-differences inequality (Corollary 2.21).
--
--   **Formalization Note.** The retired version (`martingale_bernstein_bound`) omitted the
--   nonnegativity of the scale parameters $\alpha_k$ (part of Definition 2.7), so that for
--   $\alpha_k<0$ the guard $\alpha_k = 0 \lor |\lambda| < 1/\alpha_k$ was unsatisfiable and the
--   conditional-MGF hypothesis was vacuous; it also wrote the regime split as
--   $t \le V/\alpha_*$ with Lean's total division, which for $\alpha_* = 0$ reads $t\le 0$ and
--   collapses part (b) to the trivial bound $2$ in the sub-Gaussian case. The new statement adds
--   `h_alpha : ∀ k ∈ Icc 1 n, 0 ≤ α k` and reads the regime split as
--   $\alpha_* = 0 \lor t \le V/\alpha_*$, the same $1/0=+\infty$ convention as `IsSubExponential`.
--   "Martingale difference sequence" is realized as $\mathcal F_k$-measurability of $D_k$ together
--   with $\mathbb E[D_k\mid\mathcal F_{k-1}] = 0$ for $k = 1,\dots,n$; explicit `Integrable`
--   hypotheses on each $D_k$ and each conditional-MGF exponential guard Mathlib's junk values for
--   `condExp`; part (a)'s first parameter is $\sqrt V$ to match Definition 2.7's parametrization
--   (the squared parameter appears in the exponent). Residual junk: when $V = 0$ and $\alpha_* = 0$
--   the first-regime bound $2e^{-t^2/(2\cdot 0)}$ is read by Lean as $2$ (the printed formula is
--   undefined there; all $D_k$ vanish a.s., and the bound is true but trivial). A corrected
--   theorem `martingale_bernstein_bound_nonneg` (adding only $\alpha_k \ge 0$) already exists on the
--   platform and is Proved; it keeps the $\alpha_* = 0$ collapse of part (b).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 35 (PDF p. 55), Theorem 2.19, Eq. (2.28)

import Mathlib
import Definitions.Def_HighDimStat_TailBounds_IsSubExponential

open MeasureTheory

namespace HighDimStat.TailBounds

/-- **Theorem 2.19** (Martingale Bernstein bound), Wainwright, *High-Dimensional Statistics*
(2019), p. 35, Eq. (2.28). Let `{(Dk,Fk)}` be a martingale difference sequence (realized as:
`D k` is `ℱ k`-measurable and `E[D k | ℱ (k-1)] = 0`, for `k = 1,...,n`), and suppose
`E[e^{λDk} | ℱ(k-1)] ≤ e^{λ²νk²/2}` a.s. for `|λ| < 1/αk`, where the scale parameters `αk`
are **nonnegative** (Definition 2.7: sub-exponential parameters `(ν, α)` are nonnegative, with
`1/0 = +∞`). Then (a) `∑Dk` is sub-exponential with parameters `(√(∑νk²), α* := max αk)`, and
(b) `∑Dk` satisfies the two-regime concentration inequality (2.28), where the Gaussian regime
`t ≤ ∑νk²/α*` is read with the book's convention `1/0 = +∞` (so it covers every `t ≥ 0` when
`α* = 0`). Explicit `Integrable` hypotheses on each `D k` and on each conditional-MGF
exponential block Mathlib's `condExp`/Bochner-integral junk value `0`.

Corrections relative to the retired version: `h_alpha : 0 ≤ α k` was missing (with `α k < 0`
the guard `α k = 0 ∨ |λ| < 1/α k` is unsatisfiable, so the MGF hypothesis was vacuous), and the
regime split `t ≤ ∑νk²/α*` silently became `t ≤ 0` when `α* = 0` (Lean's `x/0 = 0`), which
collapsed part (b) to the trivial bound `2` in the sub-Gaussian case `α* = 0`. -/
theorem martingale_bernstein_bound_v2 {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
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
        if (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α = 0 ∨
            t ≤ (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2) /
              (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α))
        then 2 * Real.exp (-(t ^ 2) / (2 * ∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2))
        else 2 * Real.exp (-t / (2 * Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α)) := by sorry

end HighDimStat.TailBounds
