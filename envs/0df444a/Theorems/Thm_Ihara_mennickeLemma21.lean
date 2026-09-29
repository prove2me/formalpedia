-- Prove2me | Theorems.Thm_Ihara_mennickeLemma21
-- name    : Ihara.mennickeLemma21
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/f704d293-4a71-5971-9a39-eb14157044c1
-- title:
--   Mennicke's Lemma 2.1: U centralises N_m modulo Q_m
-- statement:
--   Let $q$ be a non-zero natural number and $m$ a natural number coprime to $q$, and work in the group $SL(2, \mathtt{ZAway}\,q)$ of $2\times 2$ matrices of determinant $1$ over the ring `ZAway q`. Write $U = \mathtt{mennickeU}\,q$ for the element given by the diagonal matrix $!![\,q, 0;\, 0, \mathtt{qInv}\,q\,]$, whose determinant is $1$ because $q$ and `qInv q` are mutually inverse in `ZAway q`. Let $Q = \mathtt{mennickeQ}\,q\,m$ be the normal subgroup of $SL(2,\mathtt{ZAway}\,q)$ of that name, let $\pi$ denote the quotient homomorphism onto $SL(2,\mathtt{ZAway}\,q)/Q$, and let $N = \mathtt{principalCongruenceAway}\,m\,q\,hmq$ be the congruence subgroup of level $m$ attached to the coprimality hypothesis. The subgroup $Z = \mathtt{mennickeZ}\,q\,m\,hmq$ is the preimage under $\pi$ of the centraliser of $\pi(N)$ in the quotient. The theorem asserts the proposition $\mathtt{MennickeLemma21}\,q\,m\,hmq$, which by definition is the membership $U \in Z$: equivalently, the image of $U$ in $SL(2,\mathtt{ZAway}\,q)/Q$ commutes with the image of every element of $N$, i.e. $[U,X] \in Q$ for all $X \in N$.
--
--   This is Lemma 2.1 of Mennicke's paper on Ihara's modular group, which says that the diagonal generator $U$ centralises the principal congruence subgroup of level $m$ modulo the normal closure $Q$ of the $m$-th power of the lower unipotent generator. It is the technical input to the congruence subgroup property for $SL(2,\mathbb{Z}[1/q])$, being cited by [`Ihara.mennickeCSP_of_prime`](thm.html#Ihara.mennickeCSP_of_prime), [`Ihara.mennickeCSP_of_coprime_of_stem`](thm.html#Ihara.mennickeCSP_of_coprime_of_stem) and [`Ihara.mennickeQ_le_commutator_sup_mennickeQ_mul`](thm.html#Ihara.mennickeQ_le_commutator_sup_mennickeQ_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_mennickeLemma21.lean

import Definitions.Def_IharaMennickeCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem Ihara.mennickeLemma21 (q m : ℕ) [NeZero q] (hmq : Nat.Coprime m q) :
    Ihara.MennickeLemma21 q m hmq := by sorry
