-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45SmoothTestCutoffV1
-- name    : Kyprianou.Ch04.exercise45SmoothTestCutoffV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:30:11.913814+00:00
-- url     : https://prove2.me/theorems/61ab6cfa-aa29-46d2-afe3-719981a33d16
-- title:
--   Bounded smooth space-time test cutoff preserving the inner jet
-- statement:
--   Construct a bounded C1-time C2-space function and continuous bounded partial derivatives matching the original test jet on the compact rectangle.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv), localisation.

import Mathlib
open Set
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem exercise45SmoothTestCutoffV1 :
∀
    (f fTime fSpace fSpace2 : Real -> Real -> Real)
    (hTime : ∀ s x : Real,
      fTime s x = deriv (fun u : Real => f u x) s)
    (hSpace : ∀ s x : Real,
      fSpace s x = deriv (fun u : Real => f s u) x)
    (hSpace2 : ∀ s x : Real,
      fSpace2 s x = deriv (fun u : Real => fSpace s u) x)
    (hSmoothTime : ∀ x : Real, ContDiff Real 1 (fun s => f s x))
    (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x => f s x))
    (hJoint : ContinuousOn (fun z : Real × Real => f z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ) ∧
      ContinuousOn (fun z : Real × Real => fTime z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ) ∧
      ContinuousOn (fun z : Real × Real => fSpace z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ) ∧
      ContinuousOn (fun z : Real × Real => fSpace2 z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ))
    (n : ℕ),
    ∃ (g gt gx gxx : ℝ → ℝ → ℝ) (K : ℝ),
      0 < K ∧
      (∀ s x, gt s x = deriv (fun u : ℝ => g u x) s) ∧
      (∀ s x, gx s x = deriv (fun u : ℝ => g s u) x) ∧
      (∀ s x, gxx s x = deriv (fun u : ℝ => gx s u) x) ∧
      (∀ x, ContDiff ℝ 1 (fun s => g s x)) ∧
      (∀ s, ContDiff ℝ 2 (fun x => g s x)) ∧
      (ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧
       ContinuousOn (fun z : ℝ × ℝ => gt z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧
       ContinuousOn (fun z : ℝ × ℝ => gx z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧
       ContinuousOn (fun z : ℝ × ℝ => gxx z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)) ∧
      (∀ s x, 0 ≤ s → |g s x| ≤ K ∧ |gt s x| ≤ K ∧ |gx s x| ≤ K ∧ |gxx s x| ≤ K) ∧
      (∀ s x, 0 ≤ s → s ≤ (n : ℝ) → |x| ≤ (n : ℝ) →
        g s x = f s x ∧ gt s x = fTime s x ∧ gx s x = fSpace s x ∧ gxx s x = fSpace2 s x)
 := by
  sorry
end Kyprianou.Ch04
