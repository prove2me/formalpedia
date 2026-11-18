-- Prove2me | Theorems.Thm_KoanaKPaths_Main_recursive_sketch_step_moments
-- name    : KoanaKPaths.Main.recursive_sketch_step_moments
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T00:27:48.945243+00:00
-- url     : https://prove2.me/theorems/a61de455-323b-43ff-9e06-da2cdb624876
-- title:
--   Unnormalized moment recurrence for the recursive sign sketch
-- statement:
--   Let $S_0=\Psi,S_1,\ldots,S_k$ be the recursive sketches of Section 3.1, with width $\ell$ and an integer coefficient tensor $c$. Average over all independent uniform label signs and all independent sketch-matrix signs. For $0\le i<k$,
--
--   $$
--   \mathbb E\|S_{i+1}\|_F^2=\ell\,\mathbb E\|S_i\|_F^2,
--   \qquad
--   \mathbb E\|S_{i+1}\|_F^4\le(\ell^2+2\ell)\mathbb E\|S_i\|_F^4.
--   $$
--
--   These are the conditional sketching bounds used in the induction proving Lemma 6. Each step uses a fresh sign matrix shared by every residual word; earlier sketches do not depend on this matrix. The argument applies to any integer coefficient tensor, since the one-step moment bounds do not require zero–one coefficients. Zero dimensions are included with empty sums. The normalization defining the estimators is not used here.
-- source:
--   Tomohiro Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, printed p. 8 / PDF p. 9, proof of Lemma 6 (one-step conditional moment recurrence), using Lemma 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf

import Definitions.Def_KoanaKPaths_Main_Estimator

theorem KoanaKPaths.Main.recursive_sketch_step_moments (n k ℓ : ℕ)
    (c : (Fin k → Fin n) → ℤ) (i : ℕ) (hi : i < k) :
    KoanaKPaths.Main.uniformMean (fun w : KoanaKPaths.Main.Labels n k × KoanaKPaths.Main.SketchSigns n k ℓ =>
      (KoanaKPaths.Main.sketchFrobSq c w.1 w.2 (i+1) : ℝ)) =
        (ℓ : ℝ) * KoanaKPaths.Main.uniformMean (fun w : KoanaKPaths.Main.Labels n k × KoanaKPaths.Main.SketchSigns n k ℓ =>
          (KoanaKPaths.Main.sketchFrobSq c w.1 w.2 i : ℝ)) ∧
      KoanaKPaths.Main.uniformMean (fun w : KoanaKPaths.Main.Labels n k × KoanaKPaths.Main.SketchSigns n k ℓ =>
        (KoanaKPaths.Main.sketchFrobSq c w.1 w.2 (i+1) : ℝ)^2) ≤
        ((ℓ : ℝ)^2+2*ℓ) * KoanaKPaths.Main.uniformMean (fun w : KoanaKPaths.Main.Labels n k × KoanaKPaths.Main.SketchSigns n k ℓ =>
          (KoanaKPaths.Main.sketchFrobSq c w.1 w.2 i : ℝ)^2) := by sorry
