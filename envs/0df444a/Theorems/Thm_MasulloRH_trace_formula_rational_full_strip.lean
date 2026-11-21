-- Prove2me | Theorems.Thm_MasulloRH_trace_formula_rational_full_strip
-- name    : MasulloRH.trace_formula_rational_full_strip
-- status  : Proved
-- author  : @nlehmann
-- created : 2026-11-20T22:25:40.060339+00:00
-- url     : https://prove2.me/theorems/dcc38dd4-f1a1-46c7-8d97-b20f198b9251
-- title:
--   Weil explicit formula over all critical zeros (Masullo Thm 12.5.1.1, full strip)
-- statement:
--   This is the classical Weil explicit formula for the Riemann zeta function, written in Bombieri's form for norm-invariant test functions on the positive reals. It is the specialization of Masullo's trace formula (Theorem 12.5.1.1, rational field) in which the spectral side runs over **all** nontrivial zeros.
--
--   Let $\varphi:\mathbb R\to\mathbb C$ be smooth, with compact support contained in $(0,\infty)$, and with $\varphi(1)=0$. Write
--   $$
--   \Phi(w)=\int_0^\infty \varphi(t)\,t^{w-1}\,dt
--   $$
--   for its Mellin transform, and let $Z$ be the set of distinct zeros $\rho$ of $\zeta$ with $0<\operatorname{Re}\rho<1$, each weighted by its multiplicity $m_\rho$. Then the following hold.
--
--   1. The function $t\mapsto(\varphi(t)+\varphi(t^{-1}))\sqrt t/(t^2-1)$ is integrable on $(1,\infty)$.
--   2. The family $\frac{\log p}{p^{k/2}}\big(\varphi(p^k)+\varphi(p^{-k})\big)$, indexed by primes $p$ and integers $k\ge1$, is summable.
--   3. The family $m_\rho\,\Phi(\rho-\tfrac12)$, $\rho\in Z$, is summable (unconditionally, with no height cutoff).
--   4. The identity
--   $$
--   \int_1^\infty\big(\varphi(t)+\varphi(t^{-1})\big)\frac{\sqrt t}{t^2-1}\,dt+\sum_{p}\sum_{k\ge1}\frac{\log p}{p^{k/2}}\big(\varphi(p^k)+\varphi(p^{-k})\big)
--   =\Phi(\tfrac12)+\Phi(-\tfrac12)-\sum_{\rho\in Z}m_\rho\,\Phi(\rho-\tfrac12)
--   $$
--   holds.
--
--   With $f(x)=x^{-1/2}\varphi(x)$ and $F(s)=\int_0^\infty f(x)x^{s-1}dx=\Phi(s-\frac12)$, this is Bombieri's explicit formula
--   $$
--   \sum_\rho F(\rho)=F(0)+F(1)-\sum_{n}\Lambda(n)\big(f(n)+n^{-1}f(n^{-1})\big)-(\log4\pi+\gamma)f(1)-\int_1^\infty\Big(f(x)+x^{-1}f(x^{-1})-\frac{2f(1)}{x}\Big)\frac{x\,dx}{x^2-1},
--   $$
--   where the hypothesis $\varphi(1)=0$ removes the two terms involving $f(1)$. Equivalently, in the coordinate $g(u)=\varphi(e^u)$ it is the platform theorem `ConnesRZ.explicit_formula_C2` (an unconditional `HasSum` over all critical-strip zeros), once the Gamma-factor archimedean term there is rewritten as $-\int_0^\infty (g(u)+g(-u))\,e^{u/2}/(2\sinh u)\,du$, which is valid because $g(0)=0$.
--
--   This node isolates the unconditional, classical content of Masullo's Theorem 12.5.1.1. The restricted-strip version (`MasulloRH.trace_formula_rational`, arbitrary $\alpha>0$) follows from it together with the absence of zeros off the critical line.
--
--   **Formalization Note** The strip index `ZetaZerosInTraceStrip (1 / 2)` imposes $|\operatorname{Re}\rho-\frac12|<\frac12$, which is automatic for $0<\operatorname{Re}\rho<1$, so it ranges over all nontrivial zeros. Multiplicity is `analyticOrderNatAt riemannZeta`, the Mellin transform is Mathlib's `mellin`, and the prime-power index $(p,k)\in\texttt{Nat.Primes}\times\mathbb N$ stands for $p^{k+1}$.
-- source:
--   Weil explicit formula, in the form of E. Bombieri, Remarks on Weil's quadratic functional in the theory of prime numbers, I, Rend. Mat. Acc. Lincei s.9 v.11 (2000), 183-233 (explicit formula, §2); A. Weil, Sur les 'formules explicites' de la théorie des nombres premiers (1952). Full-strip case of A. M. Masullo, The Music of the Primes, 20 November 2026 draft, Theorem 12.5.1.1, pp.519-520. Platform form: ConnesRZ.explicit_formula_C2.

import Definitions.Def_MasulloRH_RationalTrace

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace MasulloRH

theorem trace_formula_rational_full_strip (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧
    Summable (zetaTraceTerm φ (1 / 2)) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip (1 / 2), zetaTraceTerm φ (1 / 2) ρ := by sorry

end MasulloRH
