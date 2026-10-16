-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_of_mem_ideal_span_generators
-- name    : OAI.PiExponent.FormalInterpolation.hasWeightedSupport_of_mem_ideal_span_generators
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:06:24.649351+00:00
-- url     : https://prove2.me/theorems/7c080a04-237f-4384-b650-ef271b5f4f09
-- title:
--   Weighted support preserved under ideal span
-- statement:
--   If each generator image has support bound B and every polynomial image has support bound zero, then every element of their ideal span has support bound B.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_WeightedSupport
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.hasWeightedSupport_of_mem_ideal_span_generators {m : ℕ} (v : Fin (m + 1) → ℝ) (B : ℝ) (f : MvPolynomial (Fin (m + 1)) ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ) (hf0 : ∀ Q, hasWeightedSupport v 0 (f Q)) (S : Set (MvPolynomial (Fin (m + 1)) ℂ)) (hS : ∀ Q ∈ S, hasWeightedSupport v B (f Q)) (P : MvPolynomial (Fin (m + 1)) ℂ) (hP : P ∈ Ideal.span S) : hasWeightedSupport v B (f P) := by sorry
