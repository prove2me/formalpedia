-- Prove2me | Theorems.Thm_HighDimStat_TailBounds_martingale_bernstein_bound
-- name    : HighDimStat.TailBounds.martingale_bernstein_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:21:12.875146+00:00
-- url     : https://prove2.me/theorems/85ba0a1c-b9d5-4f2d-8336-71ab5b647456
-- title:
--   Theorem 2.19 -- the martingale Bernstein bound
-- statement:
--   **Theorem 2.19 (Martingale Bernstein bound).** Let $\{(D_k,\mathcal F_k)\}_{k=1}^\infty$ be a
--   martingale difference sequence, and suppose that
--   $\mathbb E[e^{\lambda D_k}\mid\mathcal F_{k-1}]\le e^{\lambda^2\nu_k^2/2}$ almost surely for
--   any $|\lambda|<1/\alpha_k$. Then:
--
--   (a) The sum $\sum_{k=1}^n D_k$ is sub-exponential with parameters
--   $\big(\sqrt{\sum_{k=1}^n\nu_k^2},\ \alpha_*\big)$ where $\alpha_*:=\max_{k=1,\dots,n}\alpha_k$.
--
--   (b) The sum satisfies the concentration inequality
--
--   $$
--   \mathbb P\Big[\Big|\sum_{k=1}^n D_k\Big|\ge t\Big] \le
--   \begin{cases}
--   2e^{-t^2/(2\sum_{k=1}^n\nu_k^2)} & \text{if } 0\le t\le \sum_{k=1}^n\nu_k^2/\alpha_*, \\
--   2e^{-t/(2\alpha_*)} & \text{if } t > \sum_{k=1}^n\nu_k^2/\alpha_*.
--   \end{cases}
--   $$
--
--   This is the chapter's general Bernstein-type bound for martingale difference sequences,
--   obtained by controlling the moment generating function of the partial sum and applying the
--   Chernoff bound; it is the source, by specialization, of the Azuma–Hoeffding inequality
--   (Corollary 2.20) and the bounded-differences inequality (Corollary 2.21) elsewhere in this
--   mission.
--
--   **Formalization Note** "Martingale difference sequence" is realized as `ℱ k`-measurability of
--   `D k` together with `E[D k | ℱ(k-1)] = 0`, for `k=1,...,n` (`Finset.Icc 1 n`). The condition
--   `|λ|<1/αₖ` carries the same `αₖ=0 ∨ |λ|<1/αₖ` guard as `IsSubExponential`. Part (a)'s stated
--   parameter pair, printed in the book as "$(\sum\nu_k^2,\alpha_*)$", is formalized as
--   $\big(\sqrt{\sum\nu_k^2},\alpha_*\big)$ to match Definition 2.7's own parametrization
--   exactly (where the *squared* first parameter, not the parameter itself, appears in the
--   exponent): this is the value that makes part (a) consistent with part (b)'s own tail-bound
--   formula, which the book derives directly from part (a) via the general sub-exponential tail
--   bound (Proposition 2.9) — see `MODERATION_NOTES.md`. Explicit `Integrable` hypotheses on each
--   `D k` (`h_int`) and on each conditional-MGF exponential (`h_subexp_int`) are required, mirroring
--   the same guard `IsSubExponential`'s own definition uses for its bare Bochner integrals: without
--   them, Mathlib's `condExp` returns the junk value `0` on a non-integrable argument, which would
--   let `h_cent`/`h_subexp` hold vacuously for a non-integrable `D k` (e.g. Cauchy-distributed)
--   regardless of whether it is actually a martingale difference with a sub-exponential conditional
--   MGF, making the theorem false as originally stated — see `MODERATION_NOTES.md`.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 35 (PDF p. 55), Theorem 2.19, Eq. (2.28)

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
applied here to the conditional form. -/
theorem martingale_bernstein_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ℕ → Ω → ℝ} {ν α : ℕ → ℝ} {ℱ : Filtration ℕ mΩ}
    (n : ℕ) (hn : 1 ≤ n)
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
