-- Prove2me | Theorems.Thm_MasulloAudit_twisted_orbital_trace_two_sided_error
-- name    : MasulloAudit.twisted_orbital_trace_two_sided_error
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:47:12.70688+00:00
-- url     : https://prove2.me/theorems/15758781-f880-475e-bf9e-814b705a4af9
-- title:
--   Exact error of the twisted local orbital trace for two-sided test functions
-- statement:
--   Let $\varphi$ be smooth with compact support in $(0,\infty)$ and $\varphi(1)=0$, let $\Phi$ be its Mellin transform, and let $p>1$. Then all series below converge absolutely and
--
--   $$
--   \sum_{k\in\mathbb Z}\Phi\Bigl(\frac{2\pi ik}{\log p}-\frac12\Bigr)=\sum_{n\ge1}\frac{\log p}{p^{n/2}}\Bigl(\varphi(p^n)+\varphi(p^{-n})\Bigr)+\sum_{n\ge1}\log p\,\bigl(p^{n/2}-p^{-n/2}\bigr)\,\varphi(p^{-n}).
--   $$
--
--   The left side is the local orbital trace of Masullo's draft (Thm 7.4.2.1, eq. (7.4.2.1), $F=\mathbf Q$, trivial character) after the uniform $a=\tfrac12$ twist used in Chapter 11. The first sum on the right is Weil's local $p$-term (the shape of `MasulloRH.primePowerTraceTerm`). The second sum is the **exact discrepancy**: for test functions with mass below norm $1$, the uniformly twisted orbital trace overcounts it with weight $p^{n/2}-p^{-n/2}$.
--
--   Thm 11.3.2.1 assumes $\operatorname{supp}\varphi\subset C_F^{>1}$, where this discrepancy vanishes. Its application in the proof of Thm 12.5.1.1 (p. 520) only has $\varphi(C_F^1)=0$. However, that application is only to primes $p$ outside a set $S$ chosen so that $\varphi(p^{\pm n})=0$ for $n\ge1$, and there the discrepancy is also $0$. The discrepancy matters wherever the uniformly twisted trace is used at a prime with some $\varphi(p^{-n})\neq0$. See also `MasulloAudit.split_orbital_traces_eq_weil_local_term`, where opposite twists on the two sides remove the discrepancy.
--
--   **Formalization Note.** Sums are indexed by $n+1$ over $\mathbb N$, in the same style as `MasulloAudit.twisted_orbital_trace_eq_weil_local_term`. The statement allows any real $p>1$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 7.4.2.1 (p. 367), Theorem 11.3.2.1 (p. 495), proof of Theorem 12.5.1.1 (p. 520).

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Real Complex
open scoped ContDiff

namespace MasulloAudit

/-- Exact error of the uniformly twisted (`a = 1/2`) local orbital trace for two-sided tests.
For `φ` smooth with compact support in `(0, ∞)`, `φ 1 = 0` and `p > 1`,
`∑_{k ∈ ℤ} 𝓜φ(2πik / log p − 1/2)
  = ∑_{n ≥ 1} (log p / √(pⁿ)) · (φ(pⁿ) + φ(p⁻ⁿ))
    + ∑_{n ≥ 1} log p · (√(pⁿ) − 1/√(pⁿ)) · φ(p⁻ⁿ)`,
all three series being summable. The first sum is Weil's local `p`-term (`primePowerTraceTerm`
shape with `x = p^(n+1)`); the second is the mismatch: the twisted orbital trace overcounts the
part of `φ` below norm `1` by the weight `p^{n/2} − p^{−n/2}`. It vanishes when
`tsupport φ ⊆ (1, ∞)`, recovering `twisted_orbital_trace_eq_weil_local_term`. -/
theorem twisted_orbital_trace_two_sided_error (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ Set.Ioi 0) (h1 : φ 1 = 0)
    (p : ℝ) (hp : 1 < p) :
    Summable (fun k : ℤ => mellin φ (2 * π * I * k / Real.log p - 1 / 2)) ∧
    Summable (fun n : ℕ => ((Real.log p / Real.sqrt (p ^ (n + 1)) : ℝ) : ℂ) *
      (φ (p ^ (n + 1)) + φ ((p ^ (n + 1))⁻¹))) ∧
    Summable (fun n : ℕ => ((Real.log p * (Real.sqrt (p ^ (n + 1)) -
      1 / Real.sqrt (p ^ (n + 1))) : ℝ) : ℂ) * φ ((p ^ (n + 1))⁻¹)) ∧
    ∑' k : ℤ, mellin φ (2 * π * I * k / Real.log p - 1 / 2) =
      ∑' n : ℕ, ((Real.log p / Real.sqrt (p ^ (n + 1)) : ℝ) : ℂ) *
        (φ (p ^ (n + 1)) + φ ((p ^ (n + 1))⁻¹)) +
      ∑' n : ℕ, ((Real.log p * (Real.sqrt (p ^ (n + 1)) -
        1 / Real.sqrt (p ^ (n + 1))) : ℝ) : ℂ) * φ ((p ^ (n + 1))⁻¹) := by sorry

end MasulloAudit
