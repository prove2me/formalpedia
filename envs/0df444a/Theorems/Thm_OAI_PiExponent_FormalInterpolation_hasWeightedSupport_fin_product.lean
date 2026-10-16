-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_fin_product
-- name    : OAI.PiExponent.FormalInterpolation.hasWeightedSupport_fin_product
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:06:03.193808+00:00
-- url     : https://prove2.me/theorems/61df5aad-3d6d-4d33-88be-26d8aa882245
-- title:
--   Weighted support of finite products from an ideal
-- statement:
--   The image of a product of n ideal elements has weighted support at least nR; for n = 0 this follows from the zero-bound hypothesis.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_WeightedSupport
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.hasWeightedSupport_fin_product {m : ℕ} (v : Fin (m + 1) → ℝ) (R : ℝ) (n : ℕ) (f : MvPolynomial (Fin (m + 1)) ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ) (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) (hf0 : ∀ Q, hasWeightedSupport v 0 (f Q)) (hI : ∀ Q, Q ∈ I → hasWeightedSupport v R (f Q)) (s : Fin n → MvPolynomial (Fin (m + 1)) ℂ) (hs : ∀ i, s i ∈ I) : hasWeightedSupport v ((n : ℝ) * R) (f (∏ i, s i)) := by sorry
