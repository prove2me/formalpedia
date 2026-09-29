-- Prove2me | Theorems.Thm_NumberField_TateGlobal_ideleNorm_archUnitHom_eq_one_of_norm_extensionEmbedding_eq_one
-- name    : NumberField.TateGlobal.ideleNorm_archUnitHom_eq_one_of_norm_extensionEmbedding_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/95889e64-b0f9-55c1-b07a-bcd0afff8c34
-- title:
--   Idele norm one for an archimedean unit of modulus one
-- statement:
--   Let $K$ be a number field, let $v$ be an infinite place of $K$, and let $x$ be a unit of the completion $K_v$ whose image under the embedding `InfinitePlace.Completion.extensionEmbedding v` of $K_v$ into $\mathbb{C}$ has norm $1$. Consider the idele `archUnitHom v x`: its finite component is $1$, and its infinite component is the function on infinite places obtained from the constant function $1$ by updating its value at $v$ to $x$ (with inverse given by the same construction applied to $x^{-1}$). The assertion is that the idele norm of this unit is $1$, where `ideleNorm K` of a unit $a$ of the adele ring of $K$ is defined as the real number underlying the scaling factor `distribHaarChar` of the Haar measure on the adele ring under multiplication by $a$. In other words, the idele which is $x$ at $v$ and $1$ at every other place, finite or infinite, has module $1$ as soon as $|x|_v = 1$.
--
--   This is the computation of the module of an idele concentrated at a single archimedean place, in the sense of Tate's thesis. It is used in the verification that the characters $\|\cdot\|^{it}$ of the idele class group are unitary, i.e. in [`NumberField.TateGlobal.isUnitaryChar_isIdeleClassChar_localChar_archLocalChar_mul_normPowChar`](thm.html#NumberField.TateGlobal.isUnitaryChar_isIdeleClassChar_localChar_archLocalChar_mul_normPowChar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_ideleNorm_archUnitHom_eq_one_of_norm_extensionEmbedding_eq_one.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

theorem NumberField.TateGlobal.ideleNorm_archUnitHom_eq_one_of_norm_extensionEmbedding_eq_one
    (K : Type) [Field K] [NumberField K] (v : InfinitePlace K) (x : (v.Completion)ˣ)
    (hx : ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1) :
    ideleNorm K (archUnitHom v x) = 1 := by sorry
