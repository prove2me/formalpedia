-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineSegmentChainV1
-- name    : Kyprianou.Ch04.exercise42LipschitzAffineSegmentChainV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:16:15.675561+00:00
-- url     : https://prove2.me/theorems/0814ae2c-96f7-5308-acd1-40d1fa4beafd
-- title:
--   Absolute-continuity chain rule on affine segments with a Lipschitz first coordinate
-- statement:
--   For a C1 function on the nonnegative first-coordinate half-plane, an everywhere Lipschitz first-coordinate path and an affine second-coordinate path obey a two-variable chain rule integrated across a compact interval when the first coordinate stays nonnegative and is positive away from the left endpoint.
-- source:
--   Supporting deterministic calculus for Kyprianou (2006), Exercise 4.2, printed page 106.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- An affine scalar path has Lipschitz constant equal to the norm of its drift. -/
theorem kyprianou_affine_lipschitz (a c : ℝ) :
    LipschitzWith ‖c‖₊ (fun t : ℝ => a + c * t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, coe_nnnorm, Real.norm_eq_abs]
  have h : a + c * x - (a + c * y) = c * (x - y) := by ring
  rw [h, abs_mul]


/-- A C1 function along a Lipschitz coordinate and an affine coordinate is
absolutely continuous on a compact nonnegative coordinate interval. -/
theorem kyprianou_affine_comp_absolutelyContinuous
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (U : ℝ → ℝ) (K : ℝ≥0) (hU : LipschitzWith K U)
    (a c l r : ℝ) (hlr : l ≤ r)
    (hpos : ∀ s ∈ Icc l r, 0 ≤ U s) :
    AbsolutelyContinuousOnInterval (fun s : ℝ => f (U s, a + c * s)) l r := by
  let q : ℝ → ℝ × ℝ := fun s => (U s, a + c * s)
  let H : Set (ℝ × ℝ) := Set.prod (Ici (0 : ℝ)) Set.univ
  have hqLip : LipschitzWith (max K ‖c‖₊) q := by
    exact hU.prodMk (kyprianou_affine_lipschitz a c)
  have hcompact : IsCompact (q '' Icc l r) :=
    isCompact_Icc.image hqLip.continuous
  have hconv : Convex ℝ H :=
    (convex_Ici (0 : ℝ)).prod convex_univ
  have hsubset : q '' Icc l r ⊆ H := by
    rintro z ⟨s, hs, rfl⟩
    exact ⟨hpos s hs, mem_univ _⟩
  have hlocal : LocallyLipschitzOn (q '' Icc l r) f :=
    (hf.locallyLipschitzOn hconv).mono hsubset
  obtain ⟨C, hCf⟩ :=
    hlocal.exists_lipschitzOnWith_of_compact hcompact
  have hqOn : LipschitzOnWith (max K ‖c‖₊) q (Icc l r) :=
    fun _ _ _ _ => hqLip _ _
  have hcomp : LipschitzOnWith (C * max K ‖c‖₊)
      (f ∘ q) (Icc l r) :=
    hCf.comp hqOn (fun s hs => mem_image_of_mem q hs)
  have hcomp' : LipschitzOnWith (C * max K ‖c‖₊)
      (f ∘ q) (uIcc l r) := by
    simpa only [uIcc_of_le hlr] using hcomp
  simpa only [q, Function.comp_def] using hcomp'.absolutelyContinuousOnInterval


/-- A Lipschitz first coordinate and an affine second coordinate satisfy
the two-coordinate absolutely-continuous chain rule on the nonnegative halfspace. -/

theorem Kyprianou.Ch04.exercise42LipschitzAffineSegmentChainV1
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (U : ℝ → ℝ) (K : ℝ≥0) (hU : LipschitzWith K U)
    (a c l r : ℝ) (hlr : l ≤ r)
    (hNonneg : ∀ s ∈ Icc l r, 0 ≤ U s)
    (hPositive : ∀ s ∈ Ioc l r, 0 < U s) :
    f (U r, a + c * r) - f (U l, a + c * l) =
      ∫ s in l..r, fderiv ℝ f (U s, a + c * s) (1, 0) * deriv U s +
        c * fderiv ℝ f (U s, a + c * s) (0, 1) := by
  sorry
