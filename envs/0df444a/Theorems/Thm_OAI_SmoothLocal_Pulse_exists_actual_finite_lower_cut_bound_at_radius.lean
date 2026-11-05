-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Pulse_exists_actual_finite_lower_cut_bound_at_radius
-- name    : OAI.SmoothLocal.Pulse.exists_actual_finite_lower_cut_bound_at_radius
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:35.748708+00:00
-- url     : https://prove2.me/theorems/8f8b5a5a-6025-4191-a582-42c229294d39
-- title:
--   Finite-order bounds of the height on the lower cut $\theta=-r$
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $g_*$ be smooth and positive on an open $V\supseteq S$ and fix $G,Z,d,c,e_0,\kappa,q_0,L,r$ with $|q_0|\le1/20$, $0<r<1/2$, $Lr\le1/20$ and $r$ small. For each order $n$ there is $C\ge0$ such that for all $N$ and $\delta>0$, for all sufficiently large $\tau$, the following holds for every metric $g_\tau$ with $C^4$ bound $G$ and $|\det g_\tau|\ge d$ on $S$, every cap-induction height $z$ and cap-induction flow $Y$ for $g_\tau$ with $|q(0)-q_0|\le1/(100L)$, whenever $g_\tau$ is within $\tau^{-\tau}$ in $C^\tau(S)$ of the test metric $\tilde g_\tau$: every coordinate derivative of order at most $n$ of $z$ at the sheared point $(x,-r)$, $|x|\le Lr$, is bounded by $C$.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Pulse.exists_actual_finite_lower_cut_bound_at_radius` in `lean/OAI/Geometry/IsometricImmersion/Estimates/FixedRadiusCutBounds.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Estimates/FixedRadiusCutBounds.lean; Section 4.2, proof of Lemma 4.1

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation SmoothLocal.Analytic

theorem exists_actual_finite_lower_cut_bound_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G Z d c e0 kappa q0 L r : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L))
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop,
        ∀ (gTau : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
          SmoothPositiveOn gTau U → IsOpen U →
          (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) →
          CapInductionHeight gTau U Z c e0 z →
          CapInductionFlow gTau U G Z d c e0 kappa z Y W →
          |hessianQuotient gTau z 0-q0| ≤ 1/(100*L) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
              testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          ∀ ds : List (Fin 2), ds.length ≤ n → ∀ x : ℝ, |x| ≤ L*r →
            |iteratedCoordPartial ds z (inverseShearCoordinates q0 (boxPoint x (-r)))| ≤ C := by
  sorry

end SmoothLocal.Pulse
end
end OAI
