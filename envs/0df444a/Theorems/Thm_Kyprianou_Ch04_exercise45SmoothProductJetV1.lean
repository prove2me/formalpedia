-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45SmoothProductJetV1
-- name    : Kyprianou.Ch04.exercise45SmoothProductJetV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:43:41.162782+00:00
-- url     : https://prove2.me/theorems/f0e4d036-0fa0-52e6-881d-040fe99c3125
-- title:
--   Product cutoff jet identities and regularity
-- statement:
--   Multiplying a time-space test function by a smooth scalar bump in each coordinate gives the explicit product derivative jet with the required smoothness and joint continuity.
-- source:
--   Kyprianou Exercise 4.5

import Mathlib
open Set
open scoped ContDiff
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem exercise45SmoothProductJetV1 :
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
    (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b),
    let g (s x : ℝ) := b s * (b x * f s x)
    let gt (s x : ℝ) := deriv b s * (b x * f s x) + b s * (b x * fTime s x)
    let gx (s x : ℝ) := b s * (deriv b x * f s x + b x * fSpace s x)
    let gxx (s x : ℝ) := b s * (deriv (deriv b) x * f s x + deriv b x * fSpace s x +
      (deriv b x * fSpace s x + b x * fSpace2 s x))
    (∀ s x, gt s x = deriv (fun u : ℝ => g u x) s) ∧
    (∀ s x, gx s x = deriv (fun u : ℝ => g s u) x) ∧
    (∀ s x, gxx s x = deriv (fun u : ℝ => gx s u) x) ∧
    (∀ x, ContDiff ℝ 1 (fun s => g s x)) ∧
    (∀ s, ContDiff ℝ 2 (fun x => g s x)) ∧
    (ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧
     ContinuousOn (fun z : ℝ × ℝ => gt z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧
     ContinuousOn (fun z : ℝ × ℝ => gx z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧
     ContinuousOn (fun z : ℝ × ℝ => gxx z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)) := by
  sorry
end Kyprianou.Ch04
