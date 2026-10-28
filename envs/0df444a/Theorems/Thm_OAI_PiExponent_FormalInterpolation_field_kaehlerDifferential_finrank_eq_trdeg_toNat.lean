-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_field_kaehlerDifferential_finrank_eq_trdeg_toNat
-- name    : OAI.PiExponent.FormalInterpolation.field_kaehlerDifferential_finrank_eq_trdeg_toNat
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T01:04:43.743741+00:00
-- url     : https://prove2.me/theorems/93c14b45-b9b2-40fd-8df4-d55ecb69b210
-- title:
--   Differential dimension of a finite-transcendence-degree field extension
-- statement:
--   For a characteristic-zero field extension of finite transcendence degree, the dimension over the larger field of its module of Kähler differentials equals the natural number represented by its transcendence degree. A proof route uses a finite transcendence basis and the vanishing of relative differentials for the separable algebraic extension above the rational function field.

import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.FieldTheory.FinTrdeg

theorem OAI.PiExponent.FormalInterpolation.field_kaehlerDifferential_finrank_eq_trdeg_toNat
    {K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K] [FinTrdeg K L] :
    Module.finrank L (Ω[L⁄K]) = (Algebra.trdeg K L).toNat := by sorry
