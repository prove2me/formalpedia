-- Prove2me | Theorems.Thm_N25_etaAnalytic25_ne_zero
-- name    : N25.etaAnalytic25_ne_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:31:34.654187+00:00
-- url     : https://prove2.me/theorems/94ff816a-9eb4-4fa0-87f8-c47a688d9d8c
-- title:
--   The analytic eta residue function never vanishes
-- statement:
--   Let $0<g<25$ and let $\tau$ lie in the upper half-plane. Then
--
--   $$E_g(\tau)\ne0.$$
--
--   This ensures that all eta quotients defining the modular units are everywhere well defined.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.etaAnalytic25_ne_zero (g : ℕ) (hg : 0 < g) (hg25 : g < 25)
    (τ : UpperHalfPlane) : etaAnalytic25 g τ ≠ 0 := by sorry
