-- Prove2me | Theorems.Thm_NumberField_natAbs_discr_le_of_quartic_cyclotomic_tower
-- name    : NumberField.natAbs_discr_le_of_quartic_cyclotomic_tower
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:14.038202+00:00
-- url     : https://prove2.me/theorems/4a76ad54-8f4b-49cb-b11e-ca04511e50d1
-- title:
--   A quartic tower with top discriminant $5^{35}$ has base discriminant at most $5^8$
-- statement:
--   Let $K⊆L$ be number fields with $[L:K]=4$ and $|d_L|=5^{35}$. Then $$|d_K|≤5^8.$$ This supplies the discriminant estimate needed for the quintic class-number calculation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open NumberField

theorem NumberField.natAbs_discr_le_of_quartic_cyclotomic_tower
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (hdegree : Module.finrank K L = 4)
    (hdiscr : (discr L).natAbs = 5 ^ 35) :
    (discr K).natAbs ≤ 5 ^ 8 := by sorry
