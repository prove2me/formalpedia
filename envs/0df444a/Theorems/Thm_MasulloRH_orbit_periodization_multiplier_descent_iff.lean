-- Prove2me | Theorems.Thm_MasulloRH_orbit_periodization_multiplier_descent_iff
-- name    : MasulloRH.orbit_periodization_multiplier_descent_iff
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T10:20:00.194203+00:00
-- url     : https://prove2.me/theorems/0cc7755b-831f-40ba-89e8-5854491ea7e3
-- title:
--   Multiplication descends through rational-type orbit periodization exactly for invariant masks on finitely supported tests
-- statement:
--   For any subgroup acting by left translations on a group, orbit periodization is unchanged on translated inputs. A mask fixing a test of nonzero periodization but killing one translate cannot act even on their common image. On all finitely supported functions, a mask is induced by an operator on periodizations exactly when it is constant on every subgroup orbit.
-- source:
--   Masullo, Chapter 11, rational orbit and multiplicative valuation cutoffs; abstract criterion for descent prior to completion. An actual Schwartz witness requires its own test and orbit computation.

import Mathlib

theorem MasulloRH.orbit_periodization_multiplier_descent_iff (G : Type*) [Group G] (D : Subgroup G) (m : G → ℂ) :
    let P : (G → ℂ) → G → ℂ := fun f x => ∑' d : D, f ((d : G) * x)
    (∀ (f : G → ℂ) (s : D), P (fun y => f ((s : G)*y)) = P f) ∧
    (∀ (f : G → ℂ) (s : D), P f ≠ 0 →
      (∀ y, m y * f y = f y) → (∀ y, m y * f ((s:G)*y) = 0) →
      ¬ ∃ T : (G → ℂ) → G → ℂ,
        T (P f) = P (fun y => m y * f y) ∧
        T (P (fun y => f ((s:G)*y))) = P (fun y => m y * f ((s:G)*y))) ∧
    ((∃ T : (G → ℂ) → G → ℂ, ∀ f : G → ℂ, (Function.support f).Finite →
        T (P f) = P (fun y => m y * f y)) ↔ ∀ (d : D) (x : G), m ((d:G)*x) = m x) := by sorry
