-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteAtomWeightLimitV1
-- name    : Kyprianou.Ch04.finiteAtomWeightLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:17:55.182799+00:00
-- url     : https://prove2.me/theorems/10a36d1c-ad04-43d7-832c-ac6302904fc6
-- title:
--   Continuous weight limits over finitely many large atoms
-- statement:
--   Continuous weight limits over finitely many large atoms.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteAtomWeightLimitV1 (R : Measure (ℝ × ℝ)) (T : NNReal)
    (S : Finset NNReal) (j : NNReal → ℝ)
    (hs : ∀ r ∈ S, 0 < r ∧ r ≤ T)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | (1/2:ℝ) < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (Y : ℕ → NNReal → ℝ) (L : NNReal → ℝ)
    (g : ℝ → ℝ → ℝ)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Ici (0 : ℝ) ×ˢ univ))
    (h : ∀ t : NNReal, 0 < t → t ≤ T →
      Tendsto (fun n => Y n t) atTop (𝓝 (L t))) :
    Tendsto (fun n => ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
      z.2 * g z.1 (Y n z.1.toNNReal) ∂ R) atTop
      (𝓝 (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
        z.2 * g z.1 (L z.1.toNNReal) ∂ R)) := by
  sorry
end Kyprianou.Ch04
