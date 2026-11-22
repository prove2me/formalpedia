-- Prove2me | Theorems.Thm_MasulloAudit_real_place_term_eq_realTraceIntegral
-- name    : MasulloAudit.real_place_term_eq_realTraceIntegral
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:27:57.177548+00:00
-- url     : https://prove2.me/theorems/dd33eb37-9441-4d33-b0aa-239f29ce6398
-- title:
--   Real-place term of Masullo's Theorem 12.5.1.1 for $\mathbf Q$ equals the formal integral
-- statement:
--   Let $\varphi$ be an admissible test in the sense of `MasulloRH.IsRationalTraceTest`: smooth, compactly supported in $(0,\infty)$, with $\varphi(1)=0$. Regard it as the norm-invariant function $g\mapsto\varphi(|g|)$ on $\mathbf R^\times$. Then the real-place term of Masullo's Theorem 12.5.1.1, taken with the Haar measure $dx/|x|$, is absolutely convergent (no principal value is needed), and
--
--   $$
--   \frac12\int_{\mathbf R^\times}\varphi(|x|)\,\frac{|x|^{1/2}}{|1-x|}\,\frac{dx}{|x|}=\int_1^\infty\bigl(\varphi(t)+\varphi(t^{-1})\bigr)\frac{\sqrt t}{t^2-1}\,dt .
--   $$
--
--   The right side is the real-place term used in the formalization `MasulloRH.trace_formula_rational`. This theorem shows that the formalization evaluates the source's archimedean term (Theorem 12.5.1.1, p. 519, first sum, with $\mu_\infty=dx/|x|$ as in Definition A.3.2.2) correctly. The factor $\tfrac12$ is absorbed by the two sheets $x>0$ and $x<0$, and $\varphi(1)=0$ removes the singularity at $x=1$.
--
--   **Formalization Note.** The left integral is a Lebesgue integral over $\{x\neq0\}$. At $x=1$ Lean's convention $a/0=0$ applies, which affects only a null set.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 12.5.1.1 (p. 519), Definition A.3.2.2.

import Definitions.Def_MasulloRH_RationalTrace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace MasulloAudit

open MasulloRH

/-- Real-place term of Masullo, Theorem 12.5.1.1 (ζ case), for norm-invariant tests.
For `φ(g) = ϕ(|g|)` with `ϕ` an admissible rational trace test (smooth, compact support in
`(0,∞)`, `ϕ 1 = 0`), the term `½ ∫_{ℝ^×} φ(g) |g|^{1/2} / |1 - g| dμ_∞(g)` with
`dμ_∞ = dx/|x|` is an absolutely convergent Lebesgue integral (so the principal value is
an ordinary integral), and it equals `∫_{(1,∞)} realTraceIntegrand ϕ`. -/
theorem real_place_term_eq_realTraceIntegral (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IntegrableOn (fun x : ℝ => φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ))
        {x : ℝ | x ≠ 0} ∧
    (1/2 : ℂ) * ∫ x in {x : ℝ | x ≠ 0},
        φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ) =
      ∫ t in Ioi (1:ℝ), realTraceIntegrand φ t := by sorry

end MasulloAudit
