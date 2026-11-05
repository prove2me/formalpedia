-- Prove2me | Theorems.Thm_OAI_SmoothLocal_HighEquation_exists_finite_actual_Q_spatial_pointwise_bound
-- name    : OAI.SmoothLocal.HighEquation.exists_finite_actual_Q_spatial_pointwise_bound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:31.80853+00:00
-- url     : https://prove2.me/theorems/6d4bd894-3102-4af5-9fec-cc5c4a48a911
-- title:
--   Pointwise spatial bounds for the hyperbolic $Q$-form of the height equation
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Fix a shrinking slab: endpoints $x_\ell,x_r$, a speed, a time length $T$, and a length floor below the slab's width at all times. For each order $N$ there is a constant $B$ such that the following holds. Let $g$, $z$ be smooth on a coordinate rectangle containing the slab, satisfying the Darboux equation with $H_{xx}\ne0$ on the rectangle, and suppose on the slab that $Q$ has its second-jet coefficient $S_1\ge s_0>0$, with $|P_1|+\sqrt{S_1}\le$ speed, that the coordinates are bounded by $R$, that $g_{ij}$ has derivatives bounded by $G$ through order $\max(9,N+3)$ and $z$ by $Z$ through order $8$, $|\det g|\ge d$, and $|H_{xx}|\ge c$. If all derivatives of $z$ through order $\max(8,N+2)$ are at most $A$ on the initial cut $y=a$, then at every later time $t\in[a,b]$ and every $x$ in the shrunken interval,
--
--   $$\big|\partial_x^n(\partial_iz)(x,t)\big|\le B\qquad(i\in\{1,2\},\ n\le N).$$
--
--   This is the propagation of smooth tangential data along the hyperbolic region.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.HighEquation.exists_finite_actual_Q_spatial_pointwise_bound` in `lean/OAI/Geometry/IsometricImmersion/Darboux/QFiniteActual.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Darboux/QFiniteActual.lean; Section 4.2, Lemma 4.1 and (4.15)

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_finite_actual_Q_spatial_pointwise_bound
    (G R Z s0 speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2 * speed * T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b - a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      (∀ p ∈ shrinkingSlab xl xr a b speed, s0 ≤ heightQCoefficient g z 5 p) →
      (∀ p ∈ shrinkingSlab xl xr a b speed,
        |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (max 9 (N + 3)) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ max 8 (N + 2) → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      ∀ t ∈ Icc a b, ∀ x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t),
        ∀ i : Fin 2, ∀ n ≤ N,
          |spatialJet (spatialFirstJet z i) n (coordinatePoint x t)| ≤ B := by
  sorry

end SmoothLocal.HighEquation
end
end OAI
