-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicJetBound_pderiv_of_commutes
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicJetBound_pderiv_of_commutes
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:03:44.768236+00:00
-- url     : https://prove2.me/theorems/b7084bc1-2cd1-47fc-8dba-9d2f72e391a8
-- title:
--   Weighted jet vanishing is preserved under a commuting partial derivative
-- statement:
--   For any family of algebra maps whose substitutions commute with a matching successor partial derivative, a strict weighted coefficient-vanishing bound at height `H` implies the derivative bound at height `H - v i.succ`.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib.Algebra.MvPolynomial.PDeriv

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicJetBound_pderiv_of_commutes {m K : Nat} (φ : Fin K → MvPolynomial (Fin (m + 1)) Complex →ₐ[Complex] MvPowerSeries (Fin (m + 1)) Complex) (v : Fin (m + 1) → Rat) (H : Real) (i : Fin m) (F : MvPolynomial (Fin (m + 1)) Complex) (hjet : ∀ j (a : Fin (m + 1) →₀ Nat), (∑ k, (v k : Real) * (a k : Real)) < H → MvPowerSeries.coeff a (φ j F) = 0) (hcomm : ∀ j, φ j (MvPolynomial.pderiv i.succ F) = MvPowerSeries.pderiv Complex i.succ (φ j F)) : ∀ j (a : Fin (m + 1) →₀ Nat), (∑ k, (v k : Real) * (a k : Real)) < H - (v i.succ : Real) → MvPowerSeries.coeff a (φ j (MvPolynomial.pderiv i.succ F)) = 0 := by sorry
