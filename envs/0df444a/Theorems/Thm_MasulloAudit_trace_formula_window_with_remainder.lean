-- Prove2me | Theorems.Thm_MasulloAudit_trace_formula_window_with_remainder
-- name    : MasulloAudit.trace_formula_window_with_remainder
-- status  : Proved
-- author  : @lll
-- created : 2026-11-21T00:16:24.315261+00:00
-- url     : https://prove2.me/theorems/44b878a5-cce3-4960-bb2f-a81125207f2c
-- title:
--   Window explicit formula with remainder (unconditional form of Masullo's Theorem 12.5.1.1, $\zeta$ case)
-- statement:
--   For every real $\alpha$ and every admissible test $\varphi$ (smooth, compactly supported in $(0,\infty)$, $\varphi(1)=0$), with $\Phi$ the Mellin transform of $\varphi$:
--
--   $$
--   \int_1^\infty(\varphi(t)+\varphi(t^{-1}))\frac{\sqrt t}{t^2-1}\,dt+\sum_p\sum_{k\ge1}\frac{\log p}{p^{k/2}}\bigl(\varphi(p^k)+\varphi(p^{-k})\bigr)=\Phi(\tfrac12)+\Phi(-\tfrac12)-\sum_{|\operatorname{Re}\rho-\frac12|<\alpha}m_\rho\Phi(\rho-\tfrac12)-R_\alpha(\varphi),
--   $$
--
--   where the window sum runs over nontrivial zeros with $|\operatorname{Re}\rho-\tfrac12|<\alpha$, and
--
--   $$
--   R_\alpha(\varphi)=\sum_{|\operatorname{Re}\rho-\frac12|\ge\alpha}m_\rho\,\Phi(\rho-\tfrac12)
--   $$
--
--   is the contribution of the zeros outside the window. All series converge absolutely and the real-place integrand is integrable.
--
--   This is an unconditional variant of Theorem 12.5.1.1 of Masullo's draft (formalized as `MasulloRH.trace_formula_rational`), which has no term $R_\alpha$. Since $R_\alpha\equiv0$ for every $\alpha>0$ exactly when RH holds, the theorem without $R_\alpha$ is equivalent to RH, while this version is a rearrangement of Weil's explicit formula. It is the identity that holds unconditionally in place of the step left empty in §12.3 (p. 514).
--
--   **Formalization Note.** The window sum uses the same index type `ZetaZerosInTraceStrip α` as `MasulloRH.trace_formula_rational`. $R_\alpha$ is a sum over the subtype of `ZetaZerosInTraceStrip (1/2)` (all nontrivial zeros) with $\alpha\le|\operatorname{Re}\rho-\tfrac12|$. No sign condition on $\alpha$ is needed: for $\alpha\le0$ the window is empty, and for $\alpha>\tfrac12$ the remainder is empty.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 12.5.1.1 (pp. 519-520); A. Weil, Sur les formules explicites de la théorie des nombres premiers (1952).

import Definitions.Def_MasulloRH_RationalTrace

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace MasulloAudit

open MasulloRH

/-- Corrected form of Masullo, Theorem 12.5.1.1 (ζ case): the unconditional window explicit
formula with remainder. For every real α (window `1/2 + (-α, α)`) and every admissible test,
the geometric side equals `mellin φ (1/2) + mellin φ (-1/2)` minus the window zero sum minus the
remainder `R_α(φ)`, the sum of the zeta-trace terms over the zeros of the full critical strip
with `α ≤ |Re ρ - 1/2|`; both zero sums are summable. -/
theorem trace_formula_window_with_remainder (α : ℝ) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    let remainder := {ρ : ZetaZerosInTraceStrip (1 / 2) | α ≤ |(ρ : ℂ).re - 1 / 2|}
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧
    Summable (zetaTraceTerm φ α) ∧
    Summable (fun ρ : remainder => zetaTraceTerm φ (1 / 2) ρ) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        (∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) -
        ∑' ρ : remainder, zetaTraceTerm φ (1 / 2) ρ := by sorry

end MasulloAudit
