-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Geometry_every_local_immersion_has_admissible_oriented_patch
-- name    : OAI.SmoothLocal.Geometry.every_local_immersion_has_admissible_oriented_patch
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:45.125997+00:00
-- url     : https://prove2.me/theorems/fdbdad13-6ee1-4532-bb8f-193b97620497
-- title:
--   Every local immersion yields an admissible height on an oriented patch
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $g$ be a metric on the plane, $U$ a set containing $0$, and $F:\mathbb R^2\to\mathbb R^3$ a map which is a smooth isometric immersion of $(U,g)$ in the sense of the standing hypotheses. Let $D_n$ be the accumulating round disks and suppose $K_g<0$ in each open $D_n$ and $K_g=0$ on $\partial D_n$. Then for all $n_{\min},k_{\min}$ there are $n\ge n_{\min}$, $b\in\partial D_n$ and a unit vector $e\in\mathbb R^3$ normal to $F$ at $b$ with second fundamental form $\mathrm{II}_e(b)$ of rank exactly one, a rotation $R$ of the finite net, $k\ge k_{\min}$ and a centre $c$ among the oriented exterior centres such that the closed patch $\Phi(c,R,k)$ lies in $U$ and
--
--   $$z=\langle F\circ\Phi,e\rangle\text{ is a patch admissible height for the pullback metric }\Phi^*g,$$
--
--   where $\Phi(p)=c+\lambda_{n,k,R}Rp$. This is the geometric step reducing Theorem A to the whole-patch obstruction.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Geometry.every_local_immersion_has_admissible_oriented_patch` in `lean/OAI/Geometry/IsometricImmersion/Obstructions/UniversalPatchSelection.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Obstructions/UniversalPatchSelection.lean; Section 5.2, proof of Theorem A, using Lemmas 2.1 and 5.2

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

theorem every_local_immersion_has_admissible_oriented_patch
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (h0 : (0 : Coord) ∈ U)
    (hK : ∀ n : ℕ, ∀ p ∈ roundOpenDisk (accumulatingCenter n) (accumulatingRadius n),
      gaussianCurvature g p < 0)
    (hKb : ∀ n : ℕ, ∀ p ∈ frontier (accumulatingDisk n), gaussianCurvature g p = 0)
    (nmin kmin : ℕ) :
    ∃ n ≥ nmin, ∃ b ∈ frontier (accumulatingDisk n), ∃ e : Ambient,
      IsUnitNormalAt F e b ∧ secondFundamental F e b ≠ 0 ∧
      (secondFundamental F e b).rank = 1 ∧
      ∃ R : OrientationLabel, ∃ k ≥ kmin, ∃ c ∈ orientedExteriorCenters n k R,
        orientedClosedPatch n k R c ⊆ U ∧
        PatchAdmissibleHeight
          (affinePullbackMetric g c (orientedPatchScale n k R • R.val))
          (height (affinePullbackImmersion F c (orientedPatchScale n k R • R.val)) e) := by
  sorry

end SmoothLocal.Geometry
end
end OAI
