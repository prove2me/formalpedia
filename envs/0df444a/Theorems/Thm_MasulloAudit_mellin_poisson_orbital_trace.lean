-- Prove2me | Theorems.Thm_MasulloAudit_mellin_poisson_orbital_trace
-- name    : MasulloAudit.mellin_poisson_orbital_trace
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:24:13.438567+00:00
-- url     : https://prove2.me/theorems/10b9dcec-36e9-4ca9-a935-c02bd8872d27
-- title:
--   Poisson summation in Mellin form: $\sum_k\Phi(2\pi ik/\log p)=\log p\sum_n\varphi(p^n)$
-- statement:
--   Let $\varphi$ be a smooth complex-valued function with compact support in $(0,\infty)$, let $\Phi(s)=\int_0^\infty\varphi(t)t^{s}\,\frac{dt}{t}$ be its Mellin transform, and let $p>1$. Then $\sum_{k\in\mathbb Z}\Phi\!\left(\frac{2\pi i k}{\log p}\right)$ converges absolutely and
--
--   $$
--   \sum_{k\in\mathbb Z}\Phi\!\left(\frac{2\pi i k}{\log p}\right)=\log p\sum_{n\in\mathbb Z}\varphi(p^n).
--   $$
--
--   This is the Poisson-summation evaluation of the local orbital trace at a prime $p$ in Masullo's draft, Theorem 7.4.2.1, eq. (7.4.2.1). There, for $F=\mathbf Q$ and trivial character, the trace is $\sum_{\varepsilon_p}\Phi(\varepsilon_p)$ over the zeros $\varepsilon_p=2\pi i k/\log p$ of $1-p^{-s}$. After the twist $\varphi\mapsto\varphi|\cdot|^{-1/2}$, this trace equals Weil's local term $\log p\sum_{k\ge1}p^{-k/2}(\varphi(p^k)+\varphi(p^{-k}))$ for test functions supported in $\{t>1\}$, the support condition the draft imposes in Thm 11.3.2.1. For general tests the two differ by $\sum_{n\ge1}\log p\,(p^{n/2}-p^{-n/2})\,\varphi(p^{-n})$ (`MasulloAudit.twisted_orbital_trace_two_sided_error`).
--
--   **Formalization Note.** Smoothness is `ContDiff ℝ ∞`, and the support condition is `HasCompactSupport φ` with `tsupport φ ⊆ Ioi 0`. The right-hand sum is a `tsum` over `n : ℤ`; only finitely many terms are nonzero.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 7.4.2.1, eq. (7.4.2.1), p. 367; Theorem 11.3.2.1, p. 495.

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real Complex
open scoped ContDiff

namespace MasulloAudit

/-- Poisson summation in Mellin form (local orbital trace at `p`, Masullo eq. 7.4.2.1):
for `φ` smooth with compact support in `(0, ∞)` and `p > 1`,
`∑_{k ∈ ℤ} 𝓜φ(2πik / log p) = log p · ∑_{n ∈ ℤ} φ(pⁿ)`, the left side being summable. -/
theorem mellin_poisson_orbital_trace (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hpos : tsupport φ ⊆ Set.Ioi 0) (p : ℝ) (hp : 1 < p) :
    Summable (fun k : ℤ => mellin φ (2 * π * I * k / Real.log p)) ∧
    ∑' k : ℤ, mellin φ (2 * π * I * k / Real.log p) =
      (Real.log p : ℂ) * ∑' n : ℤ, φ (p ^ n) := by sorry

end MasulloAudit
