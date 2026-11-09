-- Prove2me | Theorems.Thm_HitRunGaps_Spectral_theorem_3_1
-- name    : HitRunGaps.Spectral.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:16:54.65636+00:00
-- url     : https://prove2.me/theorems/e7130a1a-3971-4525-a764-534a7d822791
-- title:
--   Theorem 3.1 — Weighted L¹ Poincaré inequality
-- statement:
--   There is a universal $C>0$ such that, for every positive dimension, convex body $K\subset\mathbb R^n$ containing a ball of radius $r>0$, and locally Lipschitz $f:\mathbb R^n\to\mathbb R$,
--
--   $$\inf_{z\in\mathbb R}\int_K|f(x)-z|\,dx\le
--   C\frac{n\sqrt{C_{PI}(\pi)}}r\int_K\delta(x)|\nabla f(x)|\,dx.$$
--
--   The constant is chosen before all dimensions, bodies, radii and functions. These are unnormalized Lebesgue integrals. The test class includes all ambient locally Lipschitz functions. This weighted L¹ inequality is the antecedent of Corollary 3.2.
--
--   Differences from the source:
--   - encoding: real finite norms and constants on their natural domain → L² equivalence classes, Lebesgue normalization and extended nonnegative variational constants; reason: A.e. equality is intrinsic to L²; uniform normalization cancels in all ratios, and infeasible infima retain +∞
--   - encoding: a convex body with uniform measure and gradient norm → the domain constants are evaluated on interior K, and the gradient norm is the norm of the scalar Fréchet derivative; reason: Convex-body boundaries have zero volume and the same inradius and boundary distance as the interior; the scalar derivative operator norm equals the Euclidean gradient norm a.e.
--   - encoding: the real infimum of nonnegative finite integrals and square root → an ENNReal infimum and the one-half power; reason: All source integrals are finite on bounded convex bodies for ambient locally Lipschitz tests, so the values agree
--   - generalization: a convex body K (compact convex set with nonempty interior) → any measurable bounded convex set with nonempty interior (open, closed or in between); reason: every compact convex body is such a set, so the statement specializes to the source's; the paper itself applies this result to the open K of Theorem 1.1, and all integrals, δ, the inradius and the constants (taken on interior K) agree for sets between the interior and the closure
--   - reading: a ball of radius r inside K → some open Euclidean ball Metric.ball c r ⊆ K, centre arbitrary; reason: the source does not say open or closed; a closed ball inside K contains the open one, so the Lean hypothesis is the weaker (more general) reading
-- source:
--   Yunbum Kook, Santosh Vempala, Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run, STOC 2027 submission #207 (October 2026), published basis, pinned PDF SHA256 a0cdd91dff374c90e51e64b6848852bf973795b9a3005c4f1ee37214f9d5a940, PDF/printed p.9, Theorem 3.1

import Definitions.Def_HitRunGaps_Spectral_Samplers

open MeasureTheory
noncomputable section

namespace HitRunGaps.Spectral

theorem theorem_3_1 : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
    ∀ K : Set (Space n), IsConvexBody K → ∀ (r : ℝ), 0 < r →
    (∃ c : Space n, Metric.ball c r ⊆ K) →
    ∀ f : Space n → ℝ, LocallyLipschitz f →
    (⨅ z : ℝ, ∫⁻ x in K, ENNReal.ofReal |f x - z|) ≤
      ENNReal.ofReal C * (n : ENNReal) * (poincare (interior K)) ^ (1 / 2 : ℝ) /
        ENNReal.ofReal r *
        ∫⁻ x in K, ENNReal.ofReal (boundaryDistance K x * ‖fderiv ℝ f x‖) := by sorry

end HitRunGaps.Spectral
