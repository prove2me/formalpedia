-- Prove2me | Theorems.Thm_MinimaxAltRegret_Main_lemma_4_5
-- name    : MinimaxAltRegret.Main.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:35.729994+00:00
-- url     : https://prove2.me/theorems/c1ea2cf6-3297-4aca-97c3-523cdfd3c642
-- title:
--   Lemma 4.5 — comparison with every continuous comparator
-- statement:
--   Let X be a full-dimensional compact convex body in R^d, with d,T positive, and let f_1,...,f_T:X to [-1,1] be convex. Let R_(T+1)=-2 sum_(t=1)^T f_t, and let F be the normalized Lebesgue log-partition potential at eta=1/10. For every comparator u in X, including boundary points, and every 0<delta<1,
--
--   $$F(R_{T+1})\ge R_{T+1}(u)-4T\delta-\frac d\eta\log(1/\delta).$$
--
--   The coefficient is exactly 4 and the dimension coefficient is d/eta=10d. No minimizer or interior restriction on u is imposed. This is equation (19), supplying the continuous comparator term in the regret estimate.
--
--   Differences from the source:
--   - encoding: rounds 1 through T and the terminal action x_(T+1) → zero-based losses and actions, with action T terminal and source score R_t stored at index t; reason: a bijective reindexing preserves every summand and includes the same terminal update
--   - encoding: a d-dimensional compact convex set X and convex functions defined on X → a compact convex subset of EuclideanSpace R (Fin d) with nonempty interior, and ambient functions restricted by ConvexOn and pointwise bounds on X; reason: nonempty interior is exactly full affine dimension; arbitrary extensions outside X change no source instance, and no continuity is required on the boundary
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 12 / PDF p. 13, Lemma 4.5, Eq. (19); SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Sampling
import Definitions.Def_MinimaxAltRegret_Main_LowerConstruction

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

theorem lemma_4_5 (d T : ℕ) (hd : 0 < d) (hT : 0 < T)
    (X : Set (Point d)) (hX : convexBody X) (f : ℕ → Point d → ℝ)
    (hf : convexLosses X T f) (u : Point d) (hu : u ∈ X)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    continuousScore T f (T+1) u - 4*(T : ℝ)*δ -
      ((d : ℝ)/(1/10))*Real.log (1/δ) ≤
      continuousF X (1/10) (continuousScore T f (T+1)) := by sorry

end MinimaxAltRegret.Main
