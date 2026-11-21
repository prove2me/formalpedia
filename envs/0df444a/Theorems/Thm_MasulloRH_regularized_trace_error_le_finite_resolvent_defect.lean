-- Prove2me | Theorems.Thm_MasulloRH_regularized_trace_error_le_finite_resolvent_defect
-- name    : MasulloRH.regularized_trace_error_le_finite_resolvent_defect
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:40:54.807604+00:00
-- url     : https://prove2.me/theorems/e8e20d90-519b-4c4d-adbe-d280b331af45
-- title:
--   A finite list of in-window zeros bounds the full regularized trace error on a bounded initial half-plane
-- statement:
--   For $\Re s>3/2$ and $|s|\le R$, let $H_\alpha(s)$ be the regularized trace in the centered open window $|\Re\rho-1/2|<\alpha$. Write $r_s(\rho)=m_\rho((s-\rho)^{-1}-(5/2-\rho)^{-1})$, where $m_\rho$ is the multiplicity. Let $F$ be any finite set of nontrivial zeros inside this window. Define the real reference mass
--   $$A=\Re\left(\frac{\zeta'}{\zeta}(3)-\frac{\zeta'}{\zeta}(5/2)-\operatorname{Arch}(3)+\operatorname{Polar}(3)\right).$$
--   Then
--   $$\left|\frac{\zeta'}{\zeta}(s)-H_\alpha(s)\right|\le 32(2R+3)(R+5/2)\left(A-\sum_{\rho\in F}\Re r_3(\rho)\right).$$
--   Any finite verified list supplies a bound for all these test points. No completeness of the list is required.
-- source:
--   Quantitative refinement of MasulloRH.single_resolvent_test (proof by Yi) for the 20 November 2026 Masullo trace specialization. Uses the independently proved zero-free rectangle up to ordinate six and the campaign’s full-strip regularized trace formula.

import Definitions.Def_MasulloRH_RegularizedTrace

set_option autoImplicit false

namespace MasulloRH

theorem regularized_trace_error_le_finite_resolvent_defect (α R : ℝ) (s : ℂ)
    (hR : ‖s‖ ≤ R) (hs : (3/2:ℝ) < s.re)
    (F : Finset (ZetaZerosInTraceStrip (1/2)))
    (hF : ∀ z ∈ F, |z.val.re-1/2| < α) :
    ‖zetaLogDeriv s - regularizedTraceRHS α s‖ ≤ (16*(2*(2*R+3)*(R+5/2))) *
      ((zetaLogDeriv 3).re - (zetaLogDeriv (5/2) + regularizedArch 3 - regularizedPolar 3).re -
        ∑ z ∈ F,(zeroResolventTerm (1/2) 3 z).re) := by sorry

end MasulloRH
