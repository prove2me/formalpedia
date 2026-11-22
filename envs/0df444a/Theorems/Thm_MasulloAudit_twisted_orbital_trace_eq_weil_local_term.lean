-- Prove2me | Theorems.Thm_MasulloAudit_twisted_orbital_trace_eq_weil_local_term
-- name    : MasulloAudit.twisted_orbital_trace_eq_weil_local_term
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:28:43.312169+00:00
-- url     : https://prove2.me/theorems/7a3ddce5-168d-4a1a-bb7c-60732b37a05f
-- title:
--   Twisted local orbital trace equals Weil's local $p$-term for tests supported in $t>1$
-- statement:
--   Let $\varphi$ be a smooth complex-valued function with compact support contained in $(1,\infty)$, let $\Phi$ be its Mellin transform, and let $p>1$. Then the series $\sum_{k\in\mathbb Z}\Phi\bigl(\tfrac{2\pi ik}{\log p}-\tfrac12\bigr)$ converges absolutely and
--
--   $$
--   \sum_{k\in\mathbb Z}\Phi\Bigl(\frac{2\pi i k}{\log p}-\frac12\Bigr)=\sum_{n\ge1}\frac{\log p}{p^{n/2}}\,\varphi(p^n).
--   $$
--
--   The left side is the local orbital trace of Masullo's draft, Theorem 7.4.2.1, eq. (7.4.2.1), at $F=\mathbf Q$, trivial character and prime $p$, after the $a=\tfrac12$ twist $\varphi\mapsto\varphi\,|\cdot|^{-1/2}$ used in Chapter 11. The right side is the prime-$p$ slice of Weil's local term, written in the shape of `MasulloRH.primePowerTraceTerm` (the $\varphi(p^{-n})$ part vanishes because of the support). So for test functions supported in $\{t>1\}$, the support condition of Thm 11.3.2.1, the orbital trace reproduces Weil's term exactly.
--
--   **Formalization Note.** Smoothness is `ContDiff ℝ ∞`, and the support condition is `HasCompactSupport φ` with `tsupport φ ⊆ Ioi 1`. The statement allows any real $p>1$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 7.4.2.1, eq. (7.4.2.1), p. 367; Theorem 11.3.2.1, p. 495.

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Real Complex
open scoped ContDiff

namespace MasulloAudit

/-- Twisted local orbital trace equals Weil's local `p`-term (Masullo eq. 7.4.2.1 after the
`a = 1/2` twist): for `φ` smooth with compact support in `(1, ∞)` and `p > 1`,
`∑_{k ∈ ℤ} 𝓜φ(2πik / log p − 1/2) = ∑_{n ≥ 1} (log p / √(pⁿ)) · φ(pⁿ)`,
the left side being summable. The summand on the right is the `primePowerTraceTerm` shape
`(log p / √x) · (φ x + φ x⁻¹)` with `x = p^(n+1)`, where `φ x⁻¹ = 0` by the support condition. -/
theorem twisted_orbital_trace_eq_weil_local_term (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ Set.Ioi 1) (p : ℝ) (hp : 1 < p) :
    Summable (fun k : ℤ => mellin φ (2 * π * I * k / Real.log p - 1 / 2)) ∧
    ∑' k : ℤ, mellin φ (2 * π * I * k / Real.log p - 1 / 2) =
      ∑' n : ℕ, ((Real.log p / Real.sqrt (p ^ (n + 1)) : ℝ) : ℂ) * φ (p ^ (n + 1)) := by sorry

end MasulloAudit
