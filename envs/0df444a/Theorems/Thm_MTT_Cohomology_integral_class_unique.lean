-- Prove2me | Theorems.Thm_MTT_Cohomology_integral_class_unique
-- name    : MTT.Cohomology.integral_class_unique
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-06T16:49:22.808744+00:00
-- url     : https://prove2.me/theorems/ec6877d5-abe5-4339-92e9-ec9b059162ce
-- title:
--   Uniqueness of the Eichler-Shimura class of a cusp form
-- statement:
--   A compactly supported cohomology class whose integral coefficient evaluations reproduce the modular integrals of a given cusp form, with the binomial normalization, is unique. Consequently any two integration maps agreeing with the analytic normalization agree identically, so the Eichler-Shimura class attached to a cusp form is well defined without further choices.
-- source:
--   Shimura, Introduction to the arithmetic theory of automorphic functions, Ch. 8; Mazur-Tate-Teitelbaum, Invent. Math. 84 (1986), §4

import Definitions.Def_MTT_Cohomology
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem MTT.Cohomology.integral_class_unique
    {N k : ℕ} (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (φ ψ : Hc N (k - 2) ℂ)
    (hφ : IntegralClass f φ) (hψ : IntegralClass f ψ) :
    φ = ψ := by sorry
