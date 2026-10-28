-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_finite_transcendence_basis
-- name    : OAI.PiExponent.FormalInterpolation.exists_finite_transcendence_basis
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:50:15.304728+00:00
-- url     : https://prove2.me/theorems/de29cbc7-3310-4cf6-8508-de057b7f0cf6
-- title:
--   Finite-index transcendence basis from finite transcendence degree
-- statement:
--   A field extension of Complex with finite transcendence degree has a transcendence basis indexed by Fin n, where n is the natural-number value of that transcendence degree.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

theorem OAI.PiExponent.FormalInterpolation.exists_finite_transcendence_basis {K : Type*} [Field K] [Algebra Complex K] (hfin : Algebra.trdeg Complex K < Cardinal.aleph0) : ∃ (n : ℕ) (x : Fin n → K), IsTranscendenceBasis Complex x ∧ (Algebra.trdeg Complex K).toNat = n := by sorry
