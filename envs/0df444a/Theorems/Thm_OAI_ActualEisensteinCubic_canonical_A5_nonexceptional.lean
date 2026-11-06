-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_nonexceptional
-- name    : OAI.ActualEisensteinCubic.canonical_A5_nonexceptional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:10:34.368745+00:00
-- url     : https://prove2.me/theorems/19e292b7-c9a5-40da-9f43-04bc8579bed7
-- title:
--   Actual Eisenstein Cubic: canonical A5 nonexceptional
-- statement:
--   The Actual Eisenstein Cubic construction uses the canonical A5 nonexceptional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L140-L182
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L140-L182

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.ActualEisensteinCubic
open AddChar MulChar

theorem OAI.ActualEisensteinCubic.canonical_A5_nonexceptional (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (j : ℕ)
    (hj0 : j ≠ 0) (hj6 : j < 6) (hj4 : j ≠ 4)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      ((χ⁻¹) ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        gaussSum (χ ^ (j + 2)) ψ * (χ ^ (j + 2))⁻¹ ε) *
      (χ ^ (j + 2))⁻¹ x := by sorry
