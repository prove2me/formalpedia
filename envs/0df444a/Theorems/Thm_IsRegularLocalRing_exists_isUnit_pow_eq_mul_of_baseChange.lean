-- Prove2me | Theorems.Thm_IsRegularLocalRing_exists_isUnit_pow_eq_mul_of_baseChange
-- name    : IsRegularLocalRing.exists_isUnit_pow_eq_mul_of_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/76ebac5d-0a3d-5fb3-b13c-1b081f5306e5
-- title:
--   Descent of an e-th root along finite étale base change
-- statement:
--   Let $R$ be a regular local commutative ring which is a domain and is complete with respect to its maximal ideal $\mathfrak m_R$ (in the sense of `IsAdicComplete`), with $\operatorname{ringKrullDim} R \le 2$. Let $s \in \mathfrak m_R$ with $s \notin \mathfrak m_R^2$, and let $e$ be a positive natural number whose image in $R$ is a unit. Let $R'$ be a local $R$-algebra which is finite and free as an $R$-module and étale over $R$, and let $B$ be a local Noetherian $R$-algebra which is a domain, is integrally closed in its fraction field, is finite as an $R$-module, and is such that the structure map $R \to B$ is injective (`FaithfulSMul`). Assume $B$ is residually trivial over $R$ in the sense that for every $b \in B$ there is $r \in R$ with $b - \operatorname{algebraMap}(r) \in \mathfrak m_B$. Assume finally that for some unit $u'$ of $R'$ there is an isomorphism of $R'$-algebras $R' \otimes_R B \cong R'[X]/(X^e - u' s)$, where $s$ is taken in $R'$ via the structure map. Then there exist a unit $u$ of $R$ and an element $\theta \in B$ with $\theta^e = \operatorname{algebraMap}(u s)$ in $B$.
--
--   This is the descent step for Kummer presentations: a radicial presentation $X^e - (\text{unit})\cdot s$ of $B$ that is only known after a finite étale local base change $R \to R'$ is shown to come from an $e$-th root of a unit multiple of the regular parameter $s$ already in $B$. It feeds the construction of such a presentation over $R$ itself in [`IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_baseChange_of_isIntegrallyClosed`](thm.html#IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_baseChange_of_isIntegrallyClosed), and thereby the analysis of tamely ramified covers of a two-dimensional regular local base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsRegularLocalRing_exists_isUnit_pow_eq_mul_of_baseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

open scoped TensorProduct

theorem IsRegularLocalRing.exists_isUnit_pow_eq_mul_of_baseChange
    {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [IsAdicComplete (maximalIdeal R) R]
    (hdim : ringKrullDim R ≤ 2)
    (s : R) (hs : s ∈ maximalIdeal R) (hs2 : s ∉ maximalIdeal R ^ 2)
    (e : ℕ) (he : 0 < e) (heR : IsUnit (e : R))
    (R' : Type*) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [Module.Finite R R'] [Module.Free R R'] [Algebra.Etale R R']
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (hres : ∀ b : B, ∃ r : R, b - algebraMap R B r ∈ maximalIdeal B)
    (u' : R'ˣ)
    (e' : R' ⊗[R] B ≃ₐ[R'] AdjoinRoot (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X])) :
    ∃ (u : Rˣ) (θ : B), θ ^ e = algebraMap R B ((u : R) * s) := by sorry
