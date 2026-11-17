-- Prove2me | Theorems.Thm_N25_characterField_comparison
-- name    : N25.characterField_comparison
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:45:38.765682+00:00
-- url     : https://prove2.me/theorems/8be90ed5-ca8e-4cd5-9915-d73360e8d997
-- title:
--   The explicit quintic field is the fixed field of the character kernel
-- statement:
--   Let $ψ:G_ℚ→(ℤ/71ℤ)^×$ be the order-five character and let $F_ψ=ℚ̄^{ker ψ}$. Then $$Gal(ℚ̄/F_ψ)=ker ψ ∧ F≅_ℚF_ψ.$$ This identifies the explicit character field with the Galois fixed field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CharacterField
import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.characterField_comparison :
    (IntermediateField.fixedField psi.ker).fixingSubgroup = psi.ker ∧
    Nonempty (characterField ≃ₐ[ℚ] IntermediateField.fixedField psi.ker) := by sorry
