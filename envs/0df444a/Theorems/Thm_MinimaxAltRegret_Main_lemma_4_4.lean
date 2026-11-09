-- Prove2me | Theorems.Thm_MinimaxAltRegret_Main_lemma_4_4
-- name    : MinimaxAltRegret.Main.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:40.4992+00:00
-- url     : https://prove2.me/theorems/ab52e578-c7d3-42c6-a9ad-29eae5d18731
-- title:
--   Lemma 4.4 — the continuous one-step potential inequality
-- statement:
--   Let X be a full-dimensional compact convex body in positive dimension, and let f_1,...,f_T:X to [-1,1] be arbitrary convex losses with T positive. Set f_0=f_(T+1)=0, h_t=f_(t-1)+f_t, use Algorithm 2's corrected density at eta=1/10, and let U be its corrected continuous potential. For every 1<=t<=T+1,
--
--   $$\int_X p_t(x)h_t(x)\,dx\le U(R_{t-1},f_{t-1})-U(R_t,f_t).$$
--
--   The final step uses the analysis score R_(T+1)=R_T-f_T. This is equation (18), the continuous potential inequality used for both options, including every original boundary value in the loss class.
--
--   Differences from the source:
--   - encoding: rounds 1 through T and the terminal action x_(T+1) → zero-based losses and actions, with action T terminal and source score R_t stored at index t; reason: a bijective reindexing preserves every summand and includes the same terminal update
--   - encoding: a d-dimensional compact convex set X and convex functions defined on X → a compact convex subset of EuclideanSpace R (Fin d) with nonempty interior, and ambient functions restricted by ConvexOn and pointwise bounds on X; reason: nonempty interior is exactly full affine dimension; arbitrary extensions outside X change no source instance, and no continuity is required on the boundary
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 12 / PDF p. 13, Lemma 4.4, Eq. (18); SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Sampling
import Definitions.Def_MinimaxAltRegret_Main_LowerConstruction

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

theorem lemma_4_4 (d T : ℕ) (hd : 0 < d) (hT : 0 < T)
    (X : Set (Point d)) (hX : convexBody X) (f : ℕ → Point d → ℝ)
    (hf : convexLosses X T f) :
    ∀ t ≤ T,
      (∫ x, continuousDensity X T f t x *
        (continuousPrevious T f t x + continuousPadded T f t x) ∂bodyMeasure X) ≤
      continuousU X (1/10) (continuousScore T f t) (continuousPrevious T f t) -
      continuousU X (1/10) (continuousScore T f (t+1)) (continuousPadded T f t) := by sorry

end MinimaxAltRegret.Main
