-- Prove2me | Theorems.Thm_NymanBeurling_moebius_polynomial_critical_strip_bound
-- name    : NymanBeurling.moebius_polynomial_critical_strip_bound
-- status  : Open
-- author  : @pragyan
-- created : 2026-11-21T04:04:48.849791+00:00
-- url     : https://prove2.me/theorems/72bd4672-9e1b-436c-8409-36d9439c2853
-- title:
--   Uniform subpower height bounds for finite Möbius Dirichlet polynomials
-- statement:
--   For every $\eta,\beta>0$, is there a constant $C\ge0$ such that
--   $$\left|\sum_{1\le d\le N}\frac{\mu(d)}{d^{\sigma+it}}\right|\le C(1+|t|)^\beta$$
--   for every finite cutoff $N$, every real ordinate $t$, and every $\sigma>1/2+\eta$? The constant is independent of $N,\sigma,t$. This is an open unconditional analytic estimate; Bagchi's Lemma 3 establishes it under RH. It is an arithmetic cancellation frontier with no damped residuals, coordinate cutoffs, or Hilbert norms in its conclusion. Together with normal-family convergence and Mellin--Plancherel, it controls the fixed-damping limit.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis, https://arxiv.org/pdf/math/0607733 . Lemma 3, p.140. This submission deliberately removes the paper's RH assumption and records the resulting assertion as an OPEN conjectural input, not as a proved theorem.

import Definitions.Def_NymanBeurling_DampedMellinFrontiers

theorem NymanBeurling.moebius_polynomial_critical_strip_bound :
    NymanBeurling.MoebiusPolynomialBoundaryBound := by sorry
