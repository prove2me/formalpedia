-- Prove2me | Theorems.Thm_ModernOnlineLearning_Aggregating_shrunk_volume
-- name    : ModernOnlineLearning.Aggregating.shrunk_volume
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:30.457009+00:00
-- url     : https://prove2.me/theorems/9b4ccd29-9872-4cdd-bcd1-6ec2f9166b7e
-- title:
--   Proof of Theorem 11.5, p. 183 — volume of the shrunken competitor set
-- statement:
--   Let $V\subseteq\mathbb R^d$ be closed, bounded, convex, and full-dimensional, with $d,T\geq1$ and $u\in V$. For the contracted set $V'=\{(T/d)/(T/d+1)u+(1/(T/d+1))w:w\in V\}$,
--
--   $$\frac{\operatorname{Vol}(V')}{\operatorname{Vol}(V)}=\frac{1}{(T/d+1)^d}.$$
--
--   With the uniform prior on $V$, this ratio is its probability of $V'$ and supplies the logarithmic term in Theorem 11.5.
--
--   **Formalization Note** Positive finite volume is stated explicitly to exclude Lean's zero and infinite measure division conventions; the source obtains these facts from full dimensionality and boundedness.
-- source:
--   Orabona, arXiv:1912.13213v10, proof of Theorem 11.5, p. 183, volume display

import Mathlib
import Definitions.Def_ModernOnlineLearning_Aggregating_ShrunkSet
set_option autoImplicit false

open MeasureTheory

namespace ModernOnlineLearning.Aggregating

/-- Volume identity from the proof of Theorem 11.5, p. 183. -/
theorem shrunk_volume {d : ℕ} (hd : 0 < d) (T : ℕ) (hT : 0 < T)
    (V : Set (EuclideanSpace ℝ (Fin d)))
    (hconv : Convex ℝ V) (hclosed : IsClosed V) (hbounded : Bornology.IsBounded V)
    (hvol_pos : 0 < volume V) (hvol_fin : volume V < ⊤)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ V) :
    volume (shrunkSet V u T) / volume V =
      ENNReal.ofReal (1 / (((T : ℝ) / (d : ℝ) + 1) ^ d)) := by sorry

end ModernOnlineLearning.Aggregating
