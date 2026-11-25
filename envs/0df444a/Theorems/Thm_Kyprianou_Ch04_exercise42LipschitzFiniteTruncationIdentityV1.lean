-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteTruncationIdentityV1
-- name    : Kyprianou.Ch04.exercise42LipschitzFiniteTruncationIdentityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:49:29.159914+00:00
-- url     : https://prove2.me/theorems/713d02d2-ef6c-46d6-980a-fcadb06c2930
-- title:
--   Fixed Lipschitz path finite truncation chain rule
-- statement:
--   A finite jump truncation satisfies the change-of-variables formula along a fixed nonnegative Lipschitz first coordinate that is positive away from zero.
-- source:
--   Supporting deterministic BV Stieltjes calculus for Kyprianou (2006), Chapter 4, Exercise 4.2.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvNNRealFiniteAffineRightCoercionV1
import Theorems.Thm_Kyprianou_Ch04_bvNNRealFiniteAffineLeftCoercionV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteJumpTelescopingV2
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteJumpFderivIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzTimeDerivativeBoundV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42LipschitzFiniteTruncationIdentityV1
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → ℝ) (omega : Omega) (c : ℝ)
    (U : NNReal → ℝ) (K : NNReal) (hULip : LipschitzWith K U)
    (hU0 : 0 ≤ U 0) (hUp : ∀ s : NNReal, 0 < s → 0 < U s)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (t : NNReal) :
    let j : Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) +
        ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    let Q : Finset (Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) +
        ∑ s ∈ S, if (s : NNReal) < u then j s else 0
    ∀ S : Finset (Ioc (0 : NNReal) t),
      f (U t,P S t) = f (U 0,X 0 omega) + c *
        (∫ u in Icc (0 : ℝ) (t : ℝ),
          fderiv ℝ f (U u.toNNReal,P S u.toNNReal) (0,1) ∂volume) +
        (∫ u in Icc (0 : ℝ) (t : ℝ),
          fderiv ℝ f (U u.toNNReal,P S u.toNNReal) (1,0) *
            deriv (fun z : ℝ => U z.toNNReal) u ∂volume) +
        ∑ s ∈ S, (f (U s,P S s) - f (U s,Q S s)) := by
  sorry
