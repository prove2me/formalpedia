-- Prove2me | Theorems.Thm_LariviereIGFR_Moments_vanMieghemDada_of_strict_igfr
-- name    : LariviereIGFR.Moments.vanMieghemDada_of_strict_igfr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:16.151367+00:00
-- url     : https://prove2.me/theorems/0ce76277-7e62-4336-b855-13dcf4bd8721
-- title:
--   p. 603, after Theorem 2 — strictly IGFR with finite (n+1)st moment ⇒ Van Mieghem–Dada conditions (a), (b)
-- statement:
--   Let $X\ge 0$ have regular density $\phi$, failure rate $h$ and generalized failure rate $g(\xi)=\xi h(\xi)$, and suppose $X$ is **strictly IGFR**: $g$ is strictly increasing on the open support $\{\xi:0<\Phi(\xi)<1\}$. Let $n$ be a positive integer with $\mathbb E[X^{n+1}]<\infty$. Then the two conditions of Van Mieghem and Dada (1999) hold:
--
--   - (a) $h(\xi)-\dfrac{n+1}{\xi}$ has at most one zero among the points $\xi>0$ with $\Phi(\xi)<1$;
--   - (b) the limit $\lim_{\xi\downarrow 0}\xi h(\xi)$ exists and
--   $$
--   \lim_{\xi\downarrow 0}\xi h(\xi)<n+1 .
--   $$
--
--   This relates IGFR laws to the regularity condition Van Mieghem and Dada use for a pricing problem.
--
--   **Formalization Note** Strict monotonicity is required on the open support only: on $(0,\alpha]$ the generalized failure rate is identically $0$, so strict monotonicity on all of $\{\Phi<1\}$ would be impossible when $\alpha>0$. Zeros of (a) are counted where $h$ is the paper's finite failure rate ($\xi>0$, $\Phi(\xi)<1$). The existence of the limit in (b) is part of the conclusion. The positive integer of the page is written $m$ in Lean.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §3, paragraph after Theorem 2 (Van Mieghem and Dada 1999)

import Mathlib
import Definitions.Def_LariviereIGFR_Moments_Setting

namespace LariviereIGFR.Moments

open MeasureTheory ProbabilityTheory Filter Topology

/-- p. 603, after Theorem 2: a strictly IGFR law with a finite `(m+1)`-st moment (`m` a positive
integer) satisfies the Van Mieghem–Dada (1999) conditions: (a) `h(ξ) - (m+1)/ξ` has at most one zero,
and (b) `lim_{ξ↓0} ξ h(ξ) < m + 1`. -/
theorem vanMieghemDada_of_strict_igfr (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : LariviereIGFR.Char.IsRegDensity μ φ)
    (hstrict : StrictMonoOn (LariviereIGFR.Char.genFailureRate μ φ) {ξ | 0 < cdf μ ξ ∧ cdf μ ξ < 1})
    (m : ℕ) (hm : 0 < m) (hmom : nthMoment μ ((m : ℝ) + 1) < ⊤) :
    Set.Subsingleton
        {ξ : ℝ | 0 < ξ ∧ cdf μ ξ < 1 ∧ LariviereIGFR.Char.failureRate μ φ ξ - ((m : ℝ) + 1) / ξ = 0} ∧
      ∃ L : ℝ, Tendsto (LariviereIGFR.Char.genFailureRate μ φ) (𝓝[>] 0) (𝓝 L) ∧ L < (m : ℝ) + 1 := by sorry

end LariviereIGFR.Moments
