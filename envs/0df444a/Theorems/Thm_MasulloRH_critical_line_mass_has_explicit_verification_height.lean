-- Prove2me | Theorems.Thm_MasulloRH_critical_line_mass_has_explicit_verification_height
-- name    : MasulloRH.critical_line_mass_has_explicit_verification_height
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:52:04.093845+00:00
-- url     : https://prove2.me/theorems/0748182a-f4f0-40da-bda7-86b30da60594
-- title:
--   An explicit finite zero height suffices to verify any prime cutoff in the critical-line mass criterion
-- statement:
--   Given $N\ge0$, put $X=N+4$, $n=\lceil 16384 X^{3/2}(1+\log X)\rceil$ and $H_N=5/2+2n$. If every zeta zero in the critical strip with $|\Im\rho|\le H_N$ is on the critical line, the finite set of all these zeros witnesses the critical-line mass comparison at cutoff $N$. Thus a failed comparison at $N$ forces an off-line zero below this explicit height. The zero tail is paid entirely by the von Mangoldt mass on the finite interval $(X,16X]$.
-- source:
--   Explicit finite localization of the open rational prime–critical-line-mass criterion bd574b97. Uses the proved full-strip regularized trace and its ordinate tail, together with the elementary Chebyshev bounds for ψ in Mathlib.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option autoImplicit false

open ArithmeticFunction Finset
namespace MasulloRH

theorem critical_line_mass_has_explicit_verification_height (N : ℕ) :
    let X := (N:ℝ)+4
    let n := ⌈16384*X^(3/2:ℝ)*(1+Real.log X)⌉₊
    let H := (5/2:ℝ)+2*(n:ℝ)
    (∀ z : ZetaZerosInTraceStrip (1/2), |z.val.im| ≤ H → z.val.re = 1/2) →
    ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
      (∀ z, z ∈ F ↔ |z.val.im| ≤ H) ∧ (∀ z ∈ F, z.val.re = 1/2) ∧
      Real.log 2/2 + Real.pi/4 - 37/30 +
        (∑ j ∈ Finset.range N, (vonMangoldt j/(j:ℝ)^(5/2:ℝ) - vonMangoldt j/(j:ℝ)^(3:ℝ))) ≤
        ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
          ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4))) := by sorry

end MasulloRH
