-- Prove2me | Theorems.Thm_GaloisRepAdic_isFlatAt_of_forall_quotient
-- name    : GaloisRepAdic.isFlatAt_of_forall_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/7260ae91-f916-505f-acf7-51b7eda4662c
-- title:
--   Flatness at p is detected on the quotients A/𝔪^{m+1}
-- statement:
--   Let $A$ be a commutative local ring and let $\rho$ be an object of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16): a finite free $A$-module $V$ with $\operatorname{rank}_A V = 2$, a monoid homomorphism from $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\operatorname{End}_A V$, and the adic continuity property that for every $n$ there is a finite-dimensional intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak m_A^{\,n}\cdot V$ for all $v \in V$. Let $p$ be a natural number. Assume that for every $m$ the base change of $\rho$ along the quotient map $A \to A/\mathfrak m_A^{\,m+1}$ (a surjection of local rings, hence local, the target being nontrivial because $\mathfrak m_A^{\,m+1} \neq A$), with module $(A/\mathfrak m_A^{\,m+1}) \otimes_A V$ and the base-changed Galois action, satisfies `IsFlatAt p`. The conclusion is that $\rho$ itself satisfies `IsFlatAt p`, i.e. the residue field of $A$ is finite and, for every ideal $I \subseteq A$ with $A/I$ finite, there exist a commutative ring $H$ carrying a cocommutative Hopf algebra structure over the subring $\mathbb Z_{(p)} \subseteq \mathbb Q$ of rationals with denominator coprime to $p$, finite and flat as a module over that subring, and a bijection $e$ from the set of $\mathbb Z_{(p)}$-algebra homomorphisms $H \to \overline{\mathbb Q}$ with its convolution product onto $V/IV$, such that $e(f\ast g) = e(f) + e(g)$ and, whenever $g(h) = \sigma(f(h))$ for all $h \in H$, $e(g)$ is the image of $e(f)$ under the action induced by $\rho(\sigma)$ on $V/IV$.
--
--   This is the continuity, or pro-representability, property of the flat condition in the sense of Mazur's deformation conditions: being flat at $p$ for a representation over a local ring follows from flatness at $p$ of all its reductions modulo the powers of the maximal ideal. It is used by [`GaloisRepAdic.flatCondition_of_forall_quotient`](thm.html#GaloisRepAdic.flatCondition_of_forall_quotient), alongside the corresponding statements for the determinant, unramifiedness and ordinarity conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isFlatAt_of_forall_quotient.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isFlatAt_of_forall_quotient {A : Type} [CommRing A]
    [IsLocalRing A] (ρ : GaloisRepAdic A) {p : ℕ}
    (h : ∀ m : ℕ,
      haveI : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
          (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m)))
      haveI : IsLocalRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      (ρ.baseChangeAlong (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (m + 1)))
          (IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective)).IsFlatAt p) :
    ρ.IsFlatAt p := by sorry
