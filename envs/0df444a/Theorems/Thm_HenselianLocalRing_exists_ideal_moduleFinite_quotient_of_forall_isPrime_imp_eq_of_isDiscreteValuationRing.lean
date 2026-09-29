-- Prove2me | Theorems.Thm_HenselianLocalRing_exists_ideal_moduleFinite_quotient_of_forall_isPrime_imp_eq_of_isDiscreteValuationRing
-- name    : HenselianLocalRing.exists_ideal_moduleFinite_quotient_of_forall_isPrime_imp_eq_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/28c3aa48-0b17-56c2-ac1d-2fadd5203452
-- title:
--   Finite flat branch through an isolated point over a henselian DVR
-- statement:
--   Let $R$ be a henselian local domain which is a discrete valuation ring, and let $\varpi \in R$ generate its maximal ideal, $\mathrm{maximalIdeal}\,R = (\varpi)$. Let $A$ be a domain which is an $R$-algebra of finite type such that $R \to A$ is injective, let $\mathfrak m \subset A$ be a maximal ideal with the image of $\varpi$ in $\mathfrak m$, and let $t \in \mathfrak m$. Assume: (isolation) every prime $P$ of $A$ with $t \in P$, the image of $\varpi$ in $P$, and $P \subseteq \mathfrak m$ equals $\mathfrak m$; and (regularity) for every $a \in A$ with $ta \in (\varpi)$ there is $s \notin \mathfrak m$ with $sa \in (\varpi)$, i.e. multiplication by $t$ is injective on $(A/\varpi A)_{\mathfrak m}$. Then there is an ideal $I \subseteq A$ such that $a \in I$ if and only if $sa \in (t)$ for some $s \notin \mathfrak m$ (the contraction of $t A_{\mathfrak m}$), with $t \in I$, $I \subseteq \mathfrak m$, the quotient $A/I$ finite as an $R$-module, multiplication by the image of $\varpi$ injective on $A/I$, and every prime $P \supseteq I$ contained in $\mathfrak m$.
--
--   This is the construction of the horizontal branch (a finite flat multisection, no section being claimed) of the hypersurface $t = 0$ through a closed point of the special fibre at which that hypersurface is isolated, as used in the contraction theory of curves over a henselian discrete valuation ring; finiteness comes from Zariski's main theorem for quasi-finite algebras over a henselian local ring. It is used in the construction of transcendental elements characterising membership in a valuation subring via Gauss valuations over a henselian local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HenselianLocalRing_exists_ideal_moduleFinite_quotient_of_forall_isPrime_imp_eq_of_isDiscreteValuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing

theorem HenselianLocalRing.exists_ideal_moduleFinite_quotient_of_forall_isPrime_imp_eq_of_isDiscreteValuationRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    {A : Type v} [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A]
    (hRA : Function.Injective (algebraMap R A))
    (𝔪 : Ideal A) [𝔪.IsMaximal] (hϖ𝔪 : algebraMap R A ϖ ∈ 𝔪)
    (t : A) (ht : t ∈ 𝔪)

    (hisol : ∀ P : Ideal A, P.IsPrime → t ∈ P → algebraMap R A ϖ ∈ P → P ≤ 𝔪 → P = 𝔪)

    (hreg : ∀ a : A, t * a ∈ Ideal.span {algebraMap R A ϖ} →
      ∃ s : A, s ∉ 𝔪 ∧ s * a ∈ Ideal.span {algebraMap R A ϖ}) :
    ∃ I : Ideal A,
      (∀ a : A, a ∈ I ↔ ∃ s : A, s ∉ 𝔪 ∧ s * a ∈ Ideal.span {t}) ∧
      t ∈ I ∧ I ≤ 𝔪 ∧
      Module.Finite R (A ⧸ I) ∧
      (∀ y : A ⧸ I, algebraMap R (A ⧸ I) ϖ * y = 0 → y = 0) ∧
      (∀ P : Ideal A, P.IsPrime → I ≤ P → P ≤ 𝔪) := by sorry
