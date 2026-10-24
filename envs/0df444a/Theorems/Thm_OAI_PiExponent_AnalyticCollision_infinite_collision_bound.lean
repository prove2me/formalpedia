-- Prove2me | Theorems.Thm_OAI_PiExponent_AnalyticCollision_infinite_collision_bound
-- name    : OAI.PiExponent.AnalyticCollision.infinite_collision_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T05:09:15.679102+00:00
-- url     : https://prove2.me/theorems/089aafb3-b89f-40ad-a96a-468fd5b8681e
-- title:
--   Infinite collision bound for determinants of Taylor sums
-- statement:
--   Expand the determinant using the entry sums. Assignments with repeated degrees inside a group give equal coefficient rows and vanish. The surviving assignments are bounded by distinct-degree geometric sums, yielding the multiplicity exponent and the convergence factor.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Mathlib.Analysis.Complex.CauchyIntegral
open scoped BigOperators

theorem OAI.PiExponent.AnalyticCollision.infinite_collision_bound {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ) (A : Matrix ι ι ℂ) (D s : ℝ) (L : ι → ℝ) (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1) (hL : ∀ i, 0 ≤ L i) (hC : ∀ a d j, ‖C a d j‖ ≤ D) (hB : ∀ i d, ‖B i d‖ ≤ L i * (s * s) ^ d) (hentry : ∀ i j, HasSum (fun d => B i d * C (group i) d j) (A i j)) : ‖A.det‖ ≤ ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)) * s ^ (∑ a : κ, (OAI.PiExponent.MinorTranslationData.multiplicity group a).choose 2) * ((1 - s)⁻¹) ^ Fintype.card ι := by sorry
