-- Prove2me | Theorems.Thm_GRH_primitive_nonprincipal_below_record_grid_certificates
-- name    : GRH.primitive_nonprincipal_below_record_grid_certificates
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T15:03:58.732599+00:00
-- url     : https://prove2.me/theorems/a7f725ef-ecef-5ae2-855e-fc5b2d31cf0a
-- title:
--   Finite Dirichlet-polynomial certificates for primitive nonprincipal characters below the record boundary
-- statement:
--   For each primitive nonprincipal character and integer $h\geq0$, a positive mesh denominator exists for the specified finite Dirichlet-polynomial tests with $b=0.8749570698$. They use cutoff $m^2$ at $(m+1)^2$ prescribed points; the proved low-height region at levels three and four can discharge individual cells. This is the remaining arithmetic certificate assertion for the primitive-character branch of the centered Möbius problem. An arbitrary conductor and arbitrarily large heights are quantified.
-- source:
--   Derived for the centered Möbius progression bound at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its primitive nonprincipal Dirichlet input at https://prove2.me/theorems/046910d8-f152-46b2-aff5-b1c00405bcd0. Uses the published Dirichlet tail estimate at https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f and the Davenport bound at https://prove2.me/theorems/c5c90f21-b770-4fe2-aad6-2ead5f8ee9c0.

import Definitions.Def_GRH_DirichletGrid

theorem GRH.primitive_nonprincipal_below_record_grid_certificates
    (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1)
    (h : ℕ) : ∃ m : ℕ, GRH.DirichletGrid.Passes ψ
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1) m := by sorry
