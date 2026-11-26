-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_normalized_closedCore_special_negative
-- name    : FourierJacobi.Algebra.normalized_closedCore_special_negative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:40:50.081508+00:00
-- url     : https://prove2.me/theorems/bd75d8c8-9eb0-5561-8937-e6425009a729
-- title:
--   Algebra: normalized closed Core special negative
-- statement:
--   The Algebra construction uses the normalized closed Core special negative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/EulerFactors.lean#L124-L135
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/EulerFactors.lean#L124-L135

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_FourierJacobi_Algebra_EulerFactors
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]

theorem FourierJacobi.Algebra.normalized_closedCore_special_negative (t a b : K)
    (ht₀ : t ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : poincare t ≠ 0) (hp : satakeNumerator a b ≠ 0)
    (hn₁ : n₁ t a b ≠ 0) (hn₂ : n₂ t a b ≠ 0)
    (hf : fourFactors a b (-t ^ 2) ≠ 0)
    (ht : 1 - t ^ 2 ≠ 0) (ht₄ : 1 - t ^ 4 ≠ 0) :
    closedCore t a b (-t) * specialNormalizer t a b (-1) = 1 := by sorry
