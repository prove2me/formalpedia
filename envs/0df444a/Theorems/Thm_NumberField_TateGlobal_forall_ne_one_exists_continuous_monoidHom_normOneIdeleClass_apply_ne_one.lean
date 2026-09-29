-- Prove2me | Theorems.Thm_NumberField_TateGlobal_forall_ne_one_exists_continuous_monoidHom_normOneIdeleClass_apply_ne_one
-- name    : NumberField.TateGlobal.forall_ne_one_exists_continuous_monoidHom_normOneIdeleClass_apply_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/3522e8eb-c0a3-56d4-bab5-66af6b8954ad
-- title:
--   Continuous characters separate points of C_F¹
-- statement:
--   Let $F$ be a number field (a field of characteristic zero, finite-dimensional over $\mathbb{Q}$ in the sense of Mathlib's `NumberField` class). Inside the unit group $(\mathbb{A}_F)^\times$ of the adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`, let [`NumberField.TateGlobal.normOneIdeles F`](def/NumberField_TateGlobalZeta.html#L16) be the kernel of the distributive Haar character of $\mathbb{A}_F$, i.e. the subgroup of ideles that scale a Haar measure on $\mathbb{A}_F$ trivially (the norm-one ideles), and let `principalIdeles (𝓞 F) F` be the range of the unit-group map induced by the structure morphism $F \to \mathbb{A}_F$, i.e. the diagonally embedded principal ideles. Form the quotient of `normOneIdeles F` by the subgroup `(principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F)`, the principal ideles intersected with the norm-one ideles regarded as a subgroup of the latter; the quotient carries the quotient of the subspace topology. The assertion is that for every element $x$ of this quotient group with $x \ne 1$ there exists a monoid homomorphism $\chi$ from the quotient to $\mathbb{C}^\times$ which is continuous and satisfies $\chi(x) \ne 1$. No unitarity or any further condition is imposed on $\chi$.
--
--   This is the point-separation statement for the continuous characters of the norm-one idele class group $C_F^1 = \mathbb{A}_F^1/(F^\times \cap \mathbb{A}_F^1)$, the half of Pontryagin duality for this group that is used in the global theory. It is invoked in the approximation of invariant band-supported functions by sums of characters, and in the cusp-synthesis and realizability steps of the converse theorem for Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_forall_ne_one_exists_continuous_monoidHom_normOneIdeleClass_apply_ne_one.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField M4aHerbrand

theorem NumberField.TateGlobal.forall_ne_one_exists_continuous_monoidHom_normOneIdeleClass_apply_ne_one
    (F : Type) [Field F] [NumberField F] :
    ∀ x : ↥(NumberField.TateGlobal.normOneIdeles F) ⧸
        (principalIdeles (𝓞 F) F).subgroupOf (NumberField.TateGlobal.normOneIdeles F),
      x ≠ 1 → ∃ χ : (↥(NumberField.TateGlobal.normOneIdeles F) ⧸
          (principalIdeles (𝓞 F) F).subgroupOf (NumberField.TateGlobal.normOneIdeles F)) →* ℂˣ,
        Continuous χ ∧ χ x ≠ 1 := by sorry
