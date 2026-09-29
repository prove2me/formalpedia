-- Prove2me | Theorems.Thm_IsAdicComplete_mem_range_algebraMap_of_pow_eq_unit_of_forall_sub_mem_maximalIdeal
-- name    : IsAdicComplete.mem_range_algebraMap_of_pow_eq_unit_of_forall_sub_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/993d67f7-610d-560d-9063-d7bccdc019a0
-- title:
--   Hensel descent of e-th roots of units to the base
-- statement:
--   Let $R$ be a commutative local Noetherian ring which is adically complete with respect to its maximal ideal $\mathfrak m_R$, let $e$ be a natural number with $e>0$ whose image in $R$ is a unit, and let $w\in R^{\times}$. Let $B$ be a commutative local ring which is an $R$-algebra whose structure map $R\to B$ is a local homomorphism (it reflects units), and assume that the residue extension is trivial in the sense that for every $b\in B$ there is an $r\in R$ with $b-\mathrm{algebraMap}\,r\in\mathfrak m_B$. Then for every $\beta\in B$ satisfying $\beta^{e}=\mathrm{algebraMap}\,(w)$, the element $\beta$ lies in the range of the structure map $R\to B$, i.e. $\beta=\mathrm{algebraMap}\,r$ for some $r\in R$. No finiteness, flatness or domain hypothesis on $B$ is imposed, and the root $r$ is not asserted to be unique.
--
--   This is the Hensel-plus-roots-of-unity descent step: over a complete local base in which $e$ is invertible, an $e$-th root of a unit living in a local extension with trivial residue extension is already in the base. It feeds the Kummer-theoretic analysis of cyclic extensions used in [`IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot`](thm.html#IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsAdicComplete_mem_range_algebraMap_of_pow_eq_unit_of_forall_sub_mem_maximalIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsAdicComplete.mem_range_algebraMap_of_pow_eq_unit_of_forall_sub_mem_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (e : ℕ) (he : 0 < e) (heR : IsUnit (e : R)) (w : Rˣ)
    {B : Type*} [CommRing B] [IsLocalRing B] [Algebra R B] [IsLocalHom (algebraMap R B)]
    (hres : ∀ b : B, ∃ r : R, b - algebraMap R B r ∈ maximalIdeal B)
    (β : B) (hβ : β ^ e = algebraMap R B w) :
    β ∈ Set.range (algebraMap R B) := by sorry
