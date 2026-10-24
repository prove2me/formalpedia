-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeal_eq_or_comaximal
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_eq_or_comaximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:13:49.788422+00:00
-- url     : https://prove2.me/theorems/0a3a0925-6541-4edb-a4eb-8234c38f45c0
-- title:
--   Equal or comaximal logarithmic center ideals
-- statement:
--   Two logarithmic center ideals with the same truncation and exponents are equal when their centers agree, and otherwise are comaximal.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_eq_or_comaximal
    {m : Nat} (c₁ c₂ : Fin m → Complex)
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat) :
    logarithmicCenterIdeal c₁ T e = logarithmicCenterIdeal c₂ T e ∨
      logarithmicCenterIdeal c₁ T e ⊔ logarithmicCenterIdeal c₂ T e = ⊤ := by sorry
