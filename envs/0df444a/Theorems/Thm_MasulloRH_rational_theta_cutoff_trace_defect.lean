-- Prove2me | Theorems.Thm_MasulloRH_rational_theta_cutoff_trace_defect
-- name    : MasulloRH.rational_theta_cutoff_trace_defect
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:26:38.931545+00:00
-- url     : https://prove2.me/theorems/f6ad556e-8b16-4c16-804f-1206003a7a7a
-- title:
--   The limiting defect of the rational theta traces is the positive off-line resolvent mass
-- statement:
--   Take the rational theta-annihilator $E_{p_n}$ with $p_n=n+1$ and the smooth positive-side regularized test $\varphi_n=\mathrm{regularizedTraceTest}(n,3)$. Here “positive-side” means the support lies above 1. Let $T_n$ be its weighted convolution on $E_{p_n}$. Such operators exist and are unique. Write $P_n$, $A_n$, and $B_n$ for the two polar terms, the Archimedean integral, and the sum of the finite-place contributions of $\varphi_n$, respectively.
--
--   The following real difference converges unconditionally:
--   $$
--   \mathrm{Re}(P_n-A_n-B_n)-\mathrm{Re}\operatorname{Tr}T_n\longrightarrow
--   \sum_{\substack{\zeta(\rho)=0,\ 0<\mathrm{Re}\rho<1\\\mathrm{Re}\rho\ne1/2}}
--   m_\rho\,\mathrm{Re}\left(\frac1{3-\rho}-\frac1{5/2-\rho}\right).
--   $$
--   Here $m_\rho$ is the complex analytic multiplicity. The right side is nonnegative and equals zero if and only if the Riemann hypothesis holds. A single index controls both the physical cutoff and the number of zeta jets admitted by the Hilbert norm.
-- source:
--   Fixed-line rational case of A. M. Masullo, The Music of the Primes, §§10.3.1, 11.3.2 and 12.5.1, read together with A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Appendix I and Corollary 2, https://arxiv.org/abs/math/9811068. The diagonal test and this limiting defect formula are an independent deduction. The regularization subtracting the exponent 2 and the single-resolvent detector at 3 are the Prove2Me reconstructions; the strict positivity calculation is due to Yi in submission eaa70854 on 0a35acdb-fbbc-407f-a9ce-f3f660e29b8d. The fixed-line unit-band repair was proposed by Calvin Yost-Wolff.

import Mathlib
import Definitions.Def_MasulloRH_RationalThetaSpace
import Definitions.Def_MasulloRH_RegularizedTrace
import Definitions.Def_MasulloGRH_HilbertNuclear
open MasulloRH MasulloGRH Filter
open scoped Topology

theorem MasulloRH.rational_theta_cutoff_trace_defect (T : ∀ n : ℕ, rationalThetaAnnihilator ((n:ℝ)+1) →L[ℂ] rationalThetaAnnihilator ((n:ℝ)+1))
    (hT : ∀ n : ℕ, IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) (T n)) :
    let D := ∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
      (zeroResolventTerm (1/2) 3 z.val).re
    Tendsto (fun n : ℕ => (cutoffPolar n 3 - (cutoffArch n 3 + cutoffPrime n 3)).re -
      (operatorTrace (T n)).re) atTop (𝓝 D) ∧
      0 ≤ D ∧ (D = 0 ↔ RiemannHypothesis) := by sorry
