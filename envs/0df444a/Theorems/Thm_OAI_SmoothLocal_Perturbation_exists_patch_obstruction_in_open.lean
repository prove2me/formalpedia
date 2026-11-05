-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_patch_obstruction_in_open
-- name    : OAI.SmoothLocal.Perturbation.exists_patch_obstruction_in_open
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:43.829148+00:00
-- url     : https://prove2.me/theorems/dce1e217-ad88-483a-848d-8b85354eb2ab
-- title:
--   Patch obstruction: metrics with no admissible height are dense
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $g_0$ be a metric on an open set $V$ with model curvature $K_{g_0}=\kappa(x^2-h(y))$ (and the standing hypotheses on $V\supseteq S$). For every nonempty open subset $O$ of the patch perturbation set, there is $\eta\in O$ such that $g=g_0+\eta$ is smooth and positive on $V$, satisfies $K_g<-\kappa/2$ on the central box, and admits no admissible height: for every $z$, there is no open $U\supseteq S$ on which $z$ is smooth and on $S$
--
--   $$\det\nabla_g^2z=K_g\det g\,(1-|dz|_g^2),\quad 1-|dz|_g^2>0,\quad(\nabla_g^2z)_{yy}\ne0,\quad\Big|\frac{(\nabla^2_gz)_{xy}}{(\nabla^2_gz)_{yy}}\Big|\le\frac1{100}.$$
--
--   This is the density assertion in Proposition 2.2, the whole-patch obstruction on the fixed square.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Perturbation.exists_patch_obstruction_in_open` in `lean/OAI/Geometry/IsometricImmersion/Obstructions/PatchResidualTheorem.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Obstructions/PatchResidualTheorem.lean; Section 2, Proposition 2.2

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Model

theorem exists_patch_obstruction_in_open
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p)
    {O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ eta ∈ O,
      SmoothPositiveOn (perturbedMetric g0 eta.val) V ∧
      (∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 eta.val) p < -kappa/2) ∧
      ∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (perturbedMetric g0 eta.val) z := by
  sorry

end SmoothLocal.Perturbation
end
end OAI
