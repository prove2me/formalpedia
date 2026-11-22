-- Prove2me | Theorems.Thm_MasulloAudit_trace_formula_rational_alpha_zero_fails
-- name    : MasulloAudit.trace_formula_rational_alpha_zero_fails
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:11:00.687203+00:00
-- url     : https://prove2.me/theorems/d78fabd6-a1f0-4b13-94bb-619eb85a2081
-- title:
--   The window-$0$ instance of Masullo's Theorem 12.5.1.1 fails ($\zeta$ case)
-- statement:
--   Masullo's Main Theorem 12.5.1.1 (pp. 519–520), in the $\zeta$ specialization formalized as `MasulloRH.trace_formula_rational`, asserts for a window $I=[-\alpha,\alpha]$ that for every admissible test $\varphi$ (smooth, compactly supported in $(0,\infty)$, $\varphi(1)=0$)
--
--   $$
--   \int_1^\infty(\varphi(t)+\varphi(t^{-1}))\frac{\sqrt t}{t^2-1}\,dt+\sum_p\sum_{k\ge1}\frac{\log p}{p^{k/2}}\bigl(\varphi(p^k)+\varphi(p^{-k})\bigr)=\Phi(\tfrac12)+\Phi(-\tfrac12)-\sum_{\rho\in Z_\alpha}m_\rho\,\Phi(\rho-\tfrac12),
--   $$
--
--   where $\Phi$ is the Mellin transform of $\varphi$, $m_\rho$ is the multiplicity of $\rho$, $Z_\alpha$ is the set of nontrivial zeros with $|\operatorname{Re}\rho-\tfrac12|<\alpha$, and the integrability and summability statements hold. This theorem proves that **the instance $\alpha=0$ fails**: it is not the case that the identity, with its integrability and summability conclusions, holds for all admissible $\varphi$ when $\alpha=0$.
--
--   At $\alpha=0$ the window is empty, so the identity would say that the geometric side equals the two pole terms alone. By Weil's explicit formula (full-strip version, Proved), that forces the sum over all nontrivial zeros to vanish for every admissible test. The separation of zeros by Mellin transforms of admissible tests then contradicts the existence of a zero on the critical line, which is certified on the platform.
--
--   **Why this instance matters.** The draft's geometric-side results are stated for all $\alpha\ge0$: Def. 10.4.3.7 (p. 473), Thm 11.3.2.1 (p. 495), and Thm 9.3.3.5, whose proof reduces to $I=\{0\}$. We found no step in them that uses $\alpha>0$. The author states that window width $0$ is obstructed (p. 37: "For $a = 0$, no trace formula can be proved for any $b\ge0$". In the notation of (1.8.2.2), $a$ is the window half-width and $b$ the Sobolev degree, not the line parameter $a=\tfrac12$ of Chapters 11–12). He also writes that this case is never used in the paper apart from the multiplicity sanity check (p. 44). This theorem confirms formally that the window-$0$ statement is false, so any correct derivation of the geometric side must use $\alpha>0$ somewhere.
--
--   **Formalization Note.** The statement is the body of `MasulloRH.trace_formula_rational` with $\alpha:=0$ (the hypothesis $0<\alpha$ dropped), negated, and it uses the same platform definitions (`Definitions.Def_MasulloRH_RationalTrace`).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf: Theorem 12.5.1.1 (pp. 519–520); Def. 10.4.3.7 (p. 473) and Thm 11.3.2.1 (p. 495) allowing α ≥ 0; §1.7.3 (p. 37) and §1.8.2.3 (p. 44) on the case a = 0.

import Definitions.Def_MasulloRH_RationalTrace
set_option autoImplicit false
open MeasureTheory Set
open scoped Topology
open MasulloRH

namespace MasulloAudit

open MasulloRH

/-- Audit of Masullo, Theorem 12.5.1.1 (ζ case) at the source-admitted endpoint α = 0
(Def 10.4.3.7, p. 473; Thm 11.3.2.1, p. 495 allow α ≥ 0). With α = 0 the windowed zero
set `ZetaZerosInTraceStrip 0` is empty, and the identity of `MasulloRH.trace_formula_rational`
(with all its convergence conjuncts) fails for some admissible test. -/
theorem trace_formula_rational_alpha_zero_fails :
    ¬ ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ 0) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip 0, zetaTraceTerm φ 0 ρ := by sorry

end MasulloAudit
