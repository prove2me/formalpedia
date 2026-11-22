-- Prove2me | Theorems.Thm_MasulloRH_signed_discriminator_joint_prime_contour_cancellation
-- name    : MasulloRH.signed_discriminator_joint_prime_contour_cancellation
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T08:16:00.060018+00:00
-- url     : https://prove2.me/theorems/27347832-b192-45c7-a484-e5e6a13b6b2c
-- title:
--   The same signed two-moment test has positive normalized prime mass and cancels the actual completed-zeta contour
-- statement:
--   There is one smooth norm test supported in (1,32) with Mellin moments at 1 and −1/2 equal to zero and a strictly positive half moment. On every fixed line 1<c≤3/2, its normalized von Mangoldt prime-power sum tends to this positive moment, and its sum with the actual normalized two-sided completed-zeta contour tends to zero as X=exp(L) goes to infinity.
-- source:
--   Masullo rational trivial-character specialization. Uses Yi’s signed discriminator, the previously proved Chebyshev PNT application, and Zeta23’s actual multiplicity-counted zero estimates and completed-zeta contour identity from anthropics/zeta-23-lean, commit 182afbf851aa42a8ae78507be83f2356d3a33260.

import Mathlib
import Definitions.Def_Zeta23_WeilEF_VerticalLine
open Filter Topology Complex MeasureTheory Zeta23 Zeta23.WeilEF Set

theorem MasulloRH.signed_discriminator_joint_prime_contour_cancellation :
    ∃ u : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ tsupport u ⊆ Ioo 1 32 ∧
      HasMellin (fun t => (u t:ℂ)) 1 0 ∧ HasMellin (fun t => (u t:ℂ)) (-(1/2):ℂ) 0 ∧
      0 < (mellin (fun t => (u t:ℂ)) (1/2:ℂ)).re ∧
      ∀ c : ℝ, 1 < c → c ≤ 3/2 →
      let P := fun L : ℝ =>
        (∑ n ∈ Finset.Ioc ⌊Real.exp L⌋₊ ⌊32*Real.exp L⌋₊,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n * u ((n:ℝ)/Real.exp L)) / Real.sqrt (Real.exp L)
      let C := fun L : ℝ =>
        let f := fun x : ℝ => Complex.exp (-(L:ℂ)/2) * (u (Real.exp (x-L)):ℂ)
        (1/(2*Real.pi):ℂ) * ∫ t : ℝ,
          (Hfn f ((c:ℂ)+t*I) + Hfn f (1-c-t*I)) * logDeriv completedRiemannZeta ((c:ℂ)+t*I)
      Tendsto P atTop (𝓝 (mellin (fun t => (u t:ℂ)) (1/2:ℂ)).re) ∧
      Tendsto (fun L => (P L:ℂ) + C L) atTop (𝓝 0) := by sorry
