-- Prove2me | Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
-- name    : M4aHerbrand.subsingleton_ideleGaloisDescent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/3288d0dd-9735-5b1f-8977-6fd71a9ffaa2
-- title:
--   Uniqueness of Galois descent data on AdeleRing R F
-- statement:
--   Let $R$ be a commutative ring that is a Dedekind domain, let $E$ and $F$ be fields, let $F$ be an $R$-algebra which is a fraction field of $R$, and let $F$ be an $E$-algebra (no compatibility between the $R$- and $E$-algebra structures is imposed). The assertion is that the type [`M4aHerbrand.IdeleGaloisDescent R E F`](def/M4aHerbrand_IdeleClassVocab.html#L28) is a subsingleton: any two of its elements are equal. An element of that type consists of three data: a monoid homomorphism `act` from the group $F \simeq_{\mathrm{alg}[E]} F$ of $E$-algebra automorphisms of $F$ to the group of ring automorphisms of the adele ring `AdeleRing R F`; the compatibility requirement that for every $E$-algebra automorphism $g$ of $F$ and every $x \in F$ one has $\mathrm{act}(g)\bigl(\iota(x)\bigr) = \iota(g x)$, where $\iota$ is the structure map $F \to$ `AdeleRing R F`; and the requirement that $\mathrm{act}(g)$ be continuous for every such $g$. Since the last two fields are propositions, the content of the conclusion is that the homomorphism `act` is uniquely determined by these conditions. Existence of such a datum is not asserted.
--
--   This is the rigidity (uniqueness) half of Galois descent for adele rings: a continuous action by ring automorphisms of the adele ring extending the Galois action on the principal copy of the global field is unique, so it is legitimate to speak of *the* Galois action on adeles. It is invoked throughout the adelic and automorphic-form layer of the development, where statements formulated over an arbitrary descent datum may thereby be transferred to any one datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_subsingleton_ideleGaloisDescent.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem M4aHerbrand.subsingleton_ideleGaloisDescent
    (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
    [Algebra R F] [IsFractionRing R F] [Algebra E F] :
    Subsingleton (M4aHerbrand.IdeleGaloisDescent R E F) := by sorry
