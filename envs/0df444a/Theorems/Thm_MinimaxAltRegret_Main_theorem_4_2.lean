-- Prove2me | Theorems.Thm_MinimaxAltRegret_Main_theorem_4_2
-- name    : MinimaxAltRegret.Main.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:45.959203+00:00
-- url     : https://prove2.me/theorems/918458de-733b-48a6-99ee-75f38ad68ca4
-- title:
--   Theorem 4.2 — both exact continuous options and quantitative bounds
-- statement:
--   For every positive dimension d, positive integer horizon T, full-dimensional compact convex set X in R^d, and every permitted adaptive sequence of convex functions X to [-1,1], Algorithm 2 at eta=1/10 satisfies the following bounds. Let B=R_T for Option I, which plays each exact barycenter, and B=E[R_T] for Option II, which samples independently from the corrected density after the current loss is committed. In both cases,
--
--   $$B\le4T,\qquad B\le14d\log(1+T/d),\qquad B\le4T\delta+10d\log(1/\delta)\quad(0<\delta<1).$$
--
--   Option I is pathwise and its means are asserted to belong to X. Option II permits adaptive random losses, uses a real probability law with the exact conditional sampling rule, and asserts integrability of the hindsight regret before its expectation is bounded. Both include the terminal mean or sample. No continuity, smoothness or Lipschitz assumption is added to the convex [-1,1] class, and d=1 remains included.
--
--   These statements preserve equation (20) and instantiate the source's O notation uniformly, instead of replacing its finer inequality by a single coarser rate.
--
--   Differences from the source:
--   - encoding: rounds 1 through T and the terminal action x_(T+1) → zero-based losses and actions, with action T terminal and source score R_t stored at index t; reason: a bijective reindexing preserves every summand and includes the same terminal update
--   - encoding: a d-dimensional compact convex set X and convex functions defined on X → a compact convex subset of EuclideanSpace R (Fin d) with nonempty interior, and ambient functions restricted by ConvexOn and pointwise bounds on X; reason: nonempty interior is exactly full affine dimension; arbitrary extensions outside X change no source instance, and no continuity is required on the boundary
--   - encoding: Option II samples from p_t with fresh randomness independent of the committed loss → SampledRun specifies the conditional density law on every pre-sampling event, using a filtration containing past interaction and the committed current loss, and requires measurable regret; reason: the conditional law is the exact sampling operation, contains no performance assumption, and excludes an adversary observing fresh current sampling; integrability is a conclusion
--   - generalization: an O(d log(1+T/d)) bound in Theorem 4.2 → the simultaneous bounds B <= 4T, B <= 14d log(1+T/d), and B <= 4T delta + 10d log(1/delta) for every 0 < delta < 1; reason: Eq. (20) and the proof on printed p. 13 / PDF p. 14 give the delta-family and boundedness bound; the uniform coefficient 14 follows by the two-regime estimates recorded in the brief and moderation notes
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 11 / PDF p. 12, Theorem 4.2; Eq. (20) and its proof, printed p. 13 / PDF p. 14; SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Sampling
import Definitions.Def_MinimaxAltRegret_Main_LowerConstruction

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

theorem theorem_4_2 :
  ∀ (d T : ℕ), 0 < d → 0 < T → ∀ X : Set (Point d), convexBody X →
  ( (∀ f : ℕ → Point d → ℝ, convexLosses X T f →
      (∀ t ≤ T, continuousAlgorithmI X T f t ∈ X) ∧
      continuousUpperBounds d T (alternatingRegret X T f (continuousAlgorithmI X T f))) ∧
    (∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (f : ℕ → Ω → Point d → ℝ) (x : ℕ → Ω → X),
      SampledRun μ X T f x →
      Integrable (fun ω => alternatingRegret X T (fun s => f s ω)
        (fun s => (x s ω).val)) μ ∧
      continuousUpperBounds d T (∫ ω, alternatingRegret X T (fun s => f s ω)
        (fun s => (x s ω).val) ∂μ))) := by sorry

end MinimaxAltRegret.Main
