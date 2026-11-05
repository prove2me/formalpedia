-- Prove2me | Theorems.Thm_OAI_SmoothLocal_HighEquation_exists_localized_actualHighRemainder_bound
-- name    : OAI.SmoothLocal.HighEquation.exists_localized_actualHighRemainder_bound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:32.142203+00:00
-- url     : https://prove2.me/theorems/01fe75b9-3822-4f1b-895b-3804f6291882
-- title:
--   $L^2$ budget for the high remainder of the differentiated Darboux equation
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Fix $G,Z,M\ge0$, $d,c>0$ and $m$ with $m+3\ge8$. There is $C\ge0$ with the following property. Let $g$ be smooth and positive on an open $U\supseteq S$ and $z$ smooth on $U$, with $C^4$ bound $G$ for $g$ on $S$, $C^8$ bound $Z$ for $z$ on $S$, $|\det g|\ge d$ and $|H_{yy}|\ge c$ on $S$. Let $V\subseteq S$ be measurable with finite volume, suppose the derivatives of $g$ through order $m+5$ are bounded by $M$ on $V$, the height state factors of total order at most $m+1$ are bounded by $B\ge1$ on $V$, and those of order at most $m+3$ have $L^2(V)$ norm at most $H$. Then the remainder $\mathcal R_m$ in the $(m+3)$-times differentiated equation satisfies
--
--   $$\|\mathcal R_m\|_{L^2(V)}\le \mathcal B(C,G,Z,d,c,B,H,V,m)<\infty,$$
--
--   where $\mathcal B$ is an explicit finite budget, and in particular $\mathcal R_m\in L^2(V)$.
--
--   This is the Sobolev product estimate for the lower-order terms in Lemma 3.3.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.HighEquation.exists_localized_actualHighRemainder_bound` in `lean/OAI/Geometry/IsometricImmersion/Energy/LocalizedRemainderL2.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Energy/LocalizedRemainderL2.lean; Section 3.1, Lemma 3.3

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

theorem exists_localized_actualHighRemainder_bound
    (G Z M : ℝ) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hM : 0 ≤ M)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U V : Set Coord),
      SmoothPositiveOn g U → IsOpen U → modelSquare ⊆ U →
      (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      (∀ p ∈ modelSquare, d ≤ |(g p).det|) →
      ContDiffOn ℝ ∞ z U →
      (∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z) →
      (∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) →
      MeasurableSet V → V ⊆ modelSquare → volume V < (⊤ : ℝ≥0∞) →
      (∀ i j k, k ≤ m + 5 → ∀ p ∈ V,
        ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ M) →
      ∀ B : ℝ, 1 ≤ B → ∀ H : ℝ≥0,
      (∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
        ∀ p ∈ V, |heightStateFactor z n j p| ≤ B) →
      (∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
        eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞)) →
      eLpNorm (actualHighRemainder g z m) 2 (volume.restrict V) ≤
        actualHighRemainderL2Budget C (heightPFirstBound G Z d c) B H V m ∧
      actualHighRemainderL2Budget C (heightPFirstBound G Z d c) B H V m < (⊤ : ℝ≥0∞) ∧
      MemLp (actualHighRemainder g z m) 2 (volume.restrict V) := by
  sorry

end SmoothLocal.HighEquation
end
end OAI
