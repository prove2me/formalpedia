-- Prove2me | Theorems.Thm_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton
-- name    : NumberField.AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/c4ac0519-87b8-5c7d-ad9b-7024cae4fc78
-- title:
--   Discreteness of the principal ideles in the idele group
-- statement:
--   Let $F$ be a number field, i.e. a field of characteristic zero that is finite-dimensional over $\mathbb{Q}$, with ring of integers $\mathcal{O}_F$, and let $(\mathbb{A}_F)^\times$ denote the unit group of the adele ring `AdeleRing (𝓞 F) F` (the product of the infinite adele ring of $F$ with the finite adele ring of $\mathcal{O}_F$ in $F$), carrying the usual topology on units. The assertion is that there exists a subset $V \subseteq (\mathbb{A}_F)^\times$ which is open and satisfies $V \cap P = \{1\}$, where $P$ is the underlying set of the subgroup [`M4aHerbrand.principalIdeles (𝓞 F) F`](def/M4aHerbrand_IdeleClassVocab.html#L16), defined as the range of the map on unit groups induced by the algebra map $F \to \mathbb{A}_F$; that is, $P$ consists of the ideles that are diagonal images of elements of $F^\times$. So the conclusion is discreteness of the group of principal ideles in the idele group, stated in the concrete form of an open set meeting it exactly in the identity.
--
--   This is the classical discreteness of $F^\times$ in $\mathbb{A}_F^\times$, in the shape required to produce Borel fundamental domains for the principal ideles inside the idele group and inside the norm-one ideles. It is used in the construction of Haar measure on the idele class group and in the integration and approximation arguments for automorphic forms on $\mathrm{GL}_1$ over $F$ that rest on it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton
    (F : Type) [Field F] [NumberField F] :
    ∃ V : Set (AdeleRing (𝓞 F) F)ˣ, IsOpen V ∧
      V ∩ (M4aHerbrand.principalIdeles (𝓞 F) F : Set (AdeleRing (𝓞 F) F)ˣ) = {1} := by sorry
