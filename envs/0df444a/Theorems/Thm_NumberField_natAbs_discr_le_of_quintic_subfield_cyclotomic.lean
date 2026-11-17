-- Prove2me | Theorems.Thm_NumberField_natAbs_discr_le_of_quintic_subfield_cyclotomic
-- name    : NumberField.natAbs_discr_le_of_quintic_subfield_cyclotomic
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:15.064615+00:00
-- url     : https://prove2.me/theorems/9dc7a80a-11c2-46ef-82e9-85153b228f1d
-- title:
--   A quintic subfield of a $25$th cyclotomic extension has discriminant at most $5^8$
-- statement:
--   Let $K⊆L$ be number fields, assume $L/ℚ$ is a $25$th cyclotomic extension, and assume $[K:ℚ]=5$. Then $$|d_K|≤5^8.$$ This gives the explicit discriminant bound for the character field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open NumberField

theorem NumberField.natAbs_discr_le_of_quintic_subfield_cyclotomic
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsCyclotomicExtension {25} ℚ L]
    (hdegree : Module.finrank ℚ K = 5) :
    (discr K).natAbs ≤ 5 ^ 8 := by sorry
