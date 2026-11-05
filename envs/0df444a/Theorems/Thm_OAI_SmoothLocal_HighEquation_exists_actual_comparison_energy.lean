-- Prove2me | Theorems.Thm_OAI_SmoothLocal_HighEquation_exists_actual_comparison_energy
-- name    : OAI.SmoothLocal.HighEquation.exists_actual_comparison_energy
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:43.007345+00:00
-- url     : https://prove2.me/theorems/97342c10-93e1-4bdc-b58d-32c1acca05ec
-- title:
--   Moving-interval energy estimate for the comparison difference
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $g_{\mathrm{ref}}$ be smooth and positive on an open set $U$ containing a compact set $S$, and fix $R,Z_0,Z,c,s_0$. There is $C\ge1$ such that for every metric $g$ and all $P,z$ smooth on an open $V\subseteq U$ with $[-\rho,\rho]\times[a,b]\subseteq V\cap S$, $C^3$ bounds $Z_0$, $Z$ on that box, $z$ a Darboux solution for $g$ with $H_{xx}\ne0$, and, along the segment between the two jets, the denominator of $Q_{g_{\mathrm{ref}}}$ at least $c$ in size and the coefficient $S_1$ at least $s_0$; if $P$ and $z$ have the same Cauchy data at $y=a$ and $2\sigma(b-a)<2w$ for the speed $\sigma=\sigma(C)$, then with $w_0=P-z$,
--
--   $$\sqrt{\mathcal E(b)}\le e^{\Lambda(b-a)}\int_a^b\|F(t)\|_{L^2(I_t)}\,dt,$$
--
--   where $\mathcal E$ is the energy of $w_0$ on the shrinking interval $I_t$ with initial half-width $w$, $F$ is the metric comparison source, and $\Lambda$ depends only on $C,Z_0,Z,s_0$.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.HighEquation.exists_actual_comparison_energy` in `lean/OAI/Geometry/IsometricImmersion/Comparison/ActualComparisonEnergy.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Comparison/ActualComparisonEnergy.lean; Section 4.4, (4.16) and (4.19)

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_comparison_energy
    {gRef : MetricField} {U S : Set Coord}
    (hgRef : SmoothPositiveOn gRef U) (hU : IsOpen U)
    (hS : IsCompact S) (hSU : S ⊆ U)
    (R Z0 Z : ℝ) (hR : 0 ≤ R) {c s0 : ℝ} (hc : 0 < c) (hs0 : 0 < s0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (g : MetricField) (P z : Coord → ℝ) (V : Set Coord)
      (boxRadius width a b : ℝ),
      IsOpen V → V ⊆ U → SmoothPositiveOn g V →
      ContDiffOn ℝ ∞ P V → ContDiffOn ℝ ∞ z V →
      0 < width → width < boxRadius → a ≤ b →
      closedRectangle (-boxRadius) boxRadius a b ⊆ V →
      closedRectangle (-boxRadius) boxRadius a b ⊆ S →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, ‖p‖ ≤ R) →
      CoordinateBound P (closedRectangle (-boxRadius) boxRadius a b) 3 Z0 →
      CoordinateBound z (closedRectangle (-boxRadius) boxRadius a b) 3 Z →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b,
        (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p) →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, covHessian g z p 0 0 ≠ 0) →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, ∀ sigma ∈ Icc (0 : ℝ) 1,
        c ≤ |stateQDenominator gRef (qHeightJetSegment P z sigma p)| ∧
          s0 ≤ qFirstCoefficient gRef 5 (qHeightJetSegment P z sigma p)) →
      (∀ x ∈ Ioo (-boxRadius) boxRadius, P (boxPoint x a)=z (boxPoint x a)) →
      (∀ x ∈ Ioo (-boxRadius) boxRadius,
        coordPartial 1 P (boxPoint x a)=coordPartial 1 z (boxPoint x a)) →
      2*comparisonEnergySpeed C*(b-a)<2*width →
      Real.sqrt (movingEnergy (-width) width a (comparisonEnergySpeed C)
        (comparisonCoefficient gRef P z 5) (comparisonDifference P z) b) ≤
        Real.exp (comparisonEnergyRate C Z0 Z s0*(b-a))*
          ∫ t in a..b, movingSourceNorm (-width) width a (comparisonEnergySpeed C)
            (metricComparisonSource g gRef P z) t := by
  sorry

end SmoothLocal.HighEquation
end
end OAI
