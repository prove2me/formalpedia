-- Prove2me | Theorems.Thm_Ideal_exists_isMaximal_forall_mem_minimalPrimes_le_imp_eq_of_finiteType
-- name    : Ideal.exists_isMaximal_forall_mem_minimalPrimes_le_imp_eq_of_finiteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/d810621d-5f5e-5136-a8c6-eef5cc4bc001
-- title:
--   A closed point on only one minimal prime of I
-- statement:
--   Let $R$ be a commutative Noetherian ring, let $A$ be a commutative $R$-algebra of finite type, and let $\mathfrak m_0$ be a maximal ideal of $R$. Let $I$ be an ideal of $A$ containing the image ideal $\mathfrak m_0 A = \operatorname{map}(R \to A)(\mathfrak m_0)$, and let $\mathfrak q$ be a minimal prime of $I$, i.e. a member of `I.minimalPrimes`: a prime ideal containing $I$ that is minimal among such. Assume that $\mathfrak q$ is not maximal, and that every prime ideal $P$ of $A$ with $\mathfrak q < P$ is maximal (so $V(\mathfrak q)$ is a one-dimensional component of $V(I)$). The conclusion asserts the existence of a maximal ideal $\mathfrak m$ of $A$ with $\mathfrak q \le \mathfrak m$ such that every minimal prime $\mathfrak q'$ of $I$ satisfying $\mathfrak q' \le \mathfrak m$ equals $\mathfrak q$; that is, the component $V(\mathfrak q)$ contains a closed point of $\operatorname{Spec} A$ lying on no other irreducible component of $V(I)$.
--
--   This is the point-choice step: on a curve component of a fibre of a finite-type algebra over a Noetherian base one may pick a closed point off all the other components. It is used in the construction underlying [`ValuationSubring.exists_transcendental_forall_over_gauss_iff_mem_of_henselianLocalRing`](thm.html#ValuationSubring.exists_transcendental_forall_over_gauss_iff_mem_of_henselianLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_exists_isMaximal_forall_mem_minimalPrimes_le_imp_eq_of_finiteType.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing

theorem Ideal.exists_isMaximal_forall_mem_minimalPrimes_le_imp_eq_of_finiteType
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (𝔪₀ : Ideal R) [𝔪₀.IsMaximal]
    (I : Ideal A) (hI : Ideal.map (algebraMap R A) 𝔪₀ ≤ I)
    (𝔮 : Ideal A) (h𝔮 : 𝔮 ∈ I.minimalPrimes) (hnm : ¬ 𝔮.IsMaximal)

    (hdim : ∀ P : Ideal A, P.IsPrime → 𝔮 < P → P.IsMaximal) :
    ∃ 𝔪 : Ideal A, 𝔪.IsMaximal ∧ 𝔮 ≤ 𝔪 ∧ ∀ 𝔮' ∈ I.minimalPrimes, 𝔮' ≤ 𝔪 → 𝔮' = 𝔮 := by sorry
