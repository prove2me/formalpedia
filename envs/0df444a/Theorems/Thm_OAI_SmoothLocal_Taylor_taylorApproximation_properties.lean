-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Taylor_taylorApproximation_properties
-- name    : OAI.SmoothLocal.Taylor.taylorApproximation_properties
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:57.302493+00:00
-- url     : https://prove2.me/theorems/a4635b8d-8736-441d-ad5b-bbf9ead06f2d
-- title:
--   Properties of the recursive Taylor comparison polynomial
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $g$ be smooth and positive on an open set $U$, let $I\subseteq\mathbb R$ be open, let $u_0,u_1$ be smooth on $I$ and $a$ real with $(x,a)\in U$ for $x\in I$, and suppose the $(0,0)$ entry of $\nabla_g^2$ of the linear Cauchy polynomial $u_0(x)+u_1(x)(y-a)$ is nonzero at each $(x,a)$. Then for each $N$, the recursively defined Taylor approximation $P_N$ is smooth on the strip $I\times\mathbb R$, has the same six-variable jet as the linear polynomial on the cut $y=a$, and its $Q_g$-residual satisfies
--
--   $$\partial_t^k\big[\mathrm{res}_{g}(P_N)(x,t)\big]\big|_{t=a}=0\qquad(x\in I,\ k<N).$$
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Taylor.taylorApproximation_properties` in `lean/OAI/Geometry/IsometricImmersion/Taylor/FiniteTaylorComparison.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Taylor/FiniteTaylorComparison.lean; Section 4.3

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem taylorApproximation_properties {g : MetricField} {U : Set Coord}
    {u0 u1 : ℝ → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I)
    (a : ℝ) (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U)
    (hxx : ∀ x ∈ I, covHessian g (linearCauchy a u0 u1) ![x, a] 0 0 ≠ 0) :
    ∀ N,
      ContDiffOn ℝ ∞ (taylorApproximation g a u0 u1 N) (spatialStrip I) ∧
      (∀ x ∈ I, qSolutionJet (taylorApproximation g a u0 u1 N) ![x, a] =
        qSolutionJet (linearCauchy a u0 u1) ![x, a]) ∧
      (∀ x ∈ I, ∀ k < N,
        iteratedDeriv k (fun t => qResidual g (taylorApproximation g a u0 u1 N) ![x, t]) a = 0) := by
  sorry

end SmoothLocal.Taylor
end
end OAI
