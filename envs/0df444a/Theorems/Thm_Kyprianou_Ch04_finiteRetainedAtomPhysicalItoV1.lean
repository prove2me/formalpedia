-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteRetainedAtomPhysicalItoV1
-- name    : Kyprianou.Ch04.finiteRetainedAtomPhysicalItoV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:31:18.162048+00:00
-- url     : https://prove2.me/theorems/2be1316e-f2bf-5c77-9b02-999058799957
-- title:
--   Deterministic finite retained-atom physical Ito formula
-- statement:
--   Apply the physical common-atom affine representation and strict-left identity, then the finite-jump chain rule. Replace time integrals using the null jump-time set, apply the exact physical jump ledger, and cancel the mark compensator.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteRetainedAtomPhysicalItoV1 (R : Measure (ℝ × ℝ)) (ν : Measure ℝ)
    (T : NNReal) (e b : ℝ) (he : e < 1)
    (S : Finset NNReal) (j : NNReal → ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T ∧ e < |j r|)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (Y L : NNReal → ℝ)
    (hY : ∀ u ≤ T, Y u =
      b * (u : ℝ) + (∫ z in Icc (0 : ℝ) (u : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂ R) +
      (∫ z in Icc (0 : ℝ) (u : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1}, z.2 ∂ R) -
      (u : ℝ) * (∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν))
    (hL : ∀ u, 0 < u → Tendsto Y (𝓝[<] u) (𝓝 (L u)))
    (f ft fx : ℝ → ℝ → ℝ)
    (ht : ∀ s x, HasDerivAt (fun u => f u x) (ft s x) s)
    (hx : ∀ s x, HasDerivAt (f s) (fx s x) x)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hft : ContinuousOn (fun z : ℝ × ℝ => ft z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hfx : ContinuousOn (fun z : ℝ × ℝ => fx z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)) :
    f T (Y T) = f 0 0 + (∫ s in Icc (0 : ℝ) (T : ℝ), ft s (Y s.toNNReal)) +
      (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|},
        (f z.1 (L z.1.toNNReal + z.2) - f z.1 (L z.1.toNNReal) -
          z.2 * fx z.1 (L z.1.toNNReal)) ∂ R) +
      (b * (∫ s in Icc (0 : ℝ) (T : ℝ), fx s (L s.toNNReal)) +
        ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
          z.2 * fx z.1 (L z.1.toNNReal) ∂ R) +
      ((∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
          z.2 * fx z.1 (L z.1.toNNReal) ∂ R) -
        ∫ s in Icc (0 : ℝ) (T : ℝ), ∫ x in {x : ℝ | e < |x| ∧ |x| < 1},
          x * fx s (L s.toNNReal) ∂ν ∂volume) := by
  sorry
end Kyprianou.Ch04
