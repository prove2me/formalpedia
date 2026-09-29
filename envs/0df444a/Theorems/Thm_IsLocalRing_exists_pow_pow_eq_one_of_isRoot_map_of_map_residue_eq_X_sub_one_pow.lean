-- Prove2me | Theorems.Thm_IsLocalRing_exists_pow_pow_eq_one_of_isRoot_map_of_map_residue_eq_X_sub_one_pow
-- name    : IsLocalRing.exists_pow_pow_eq_one_of_isRoot_map_of_map_residue_eq_X_sub_one_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/c63fe251-1343-5e4c-ae32-ef0e38692cb0
-- title:
--   Roots of unity of a polynomial reducing to (X-1)^{deg} have p-power order
-- statement:
--   Let $R$ be a commutative local ring, let $p$ be a prime and assume the residue field of $R$ has characteristic $p$. Let $P \in R[X]$ be a polynomial whose image under the residue map $R \to R/\mathfrak{m}$ is $(X-1)^{n}$, where $n$ is the `natDegree` of $P$. Let $S$ be a commutative ring, let $j \colon R \to S$ be a ring homomorphism, and let $\zeta \in S$ be a root of the image $P^{j} \in S[X]$ of $P$ under $j$, i.e. $P^{j}(\zeta) = 0$. Assume further that $\zeta$ is a root of unity of some positive order, in the sense that $\zeta^{d} = 1$ for some natural number $d > 0$. Then there exists a natural number $n$ with $\zeta^{p^{n}} = 1$; that is, $\zeta$ is a $p$-power root of unity. No hypothesis of flatness, reducedness or domain-ness is imposed on $S$, and $j$ is an arbitrary ring homomorphism, not assumed injective.
--
--   A local-algebra lemma about roots of unity annihilated by a polynomial that is congruent to $(X-1)^{\deg P}$ modulo the maximal ideal: any such root of unity of finite order has order a power of the residue characteristic. It is used in the proof of [`CuspForm.IsNewform.ne_one_and_exists_pow_pow_eq_one_of_isCuspidalOfType_of_unipotentOnInertia_of_irreducible_odd`](thm.html#CuspForm.IsNewform.ne_one_and_exists_pow_pow_eq_one_of_isCuspidalOfType_of_unipotentOnInertia_of_irreducible_odd), where the roots of unity arising from a unipotent inertia action are constrained in this way.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_pow_pow_eq_one_of_isRoot_map_of_map_residue_eq_X_sub_one_pow.lean

import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem IsLocalRing.exists_pow_pow_eq_one_of_isRoot_map_of_map_residue_eq_X_sub_one_pow
    {R : Type} [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (P : R[X]) (hP : P.map (IsLocalRing.residue R) = (X - 1) ^ P.natDegree)
    {S : Type} [CommRing S] (j : R →+* S) (ζ : S) (hζ : (P.map j).IsRoot ζ)
    {d : ℕ} (hd : 0 < d) (hζd : ζ ^ d = 1) :
    ∃ n : ℕ, ζ ^ p ^ n = 1 := by sorry
