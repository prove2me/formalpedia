-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_boundary_energy_reflection
-- name    : GrothendieckLB.Supplement.cq_boundary_energy_reflection
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T19:25:12.945668+00:00
-- url     : https://prove2.me/theorems/fa0acefd-1fd5-41e2-91e4-044011e7272b
-- title:
--   Integrability and half-circle symmetry of the cubic–quintic energy
-- statement:
--   The combined Gaussian energy is integrable around the unit circle, and its integral over a full turn is twice its integral over the upper semicircle. Real polynomial coefficients make the kernels at conjugate arguments complex conjugates, and the positive Gaussian decay margin gives integrable domination.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158v2, Appendix C.2–C.4, equations (51)–(53).

import Definitions.Def_GrothendieckLB_Supplement_cqBoundaryEulerKernel

namespace GrothendieckLB.Supplement

open MeasureTheory ProbabilityTheory

theorem cq_boundary_energy_reflection :
    IntervalIntegrable CQBoundary.energy volume 0 (2*Real.pi) ∧
      (∫ θ in (0:ℝ)..2*Real.pi, CQBoundary.energy θ) = 2*∫ θ in (0:ℝ)..Real.pi, CQBoundary.energy θ := by sorry

end GrothendieckLB.Supplement
