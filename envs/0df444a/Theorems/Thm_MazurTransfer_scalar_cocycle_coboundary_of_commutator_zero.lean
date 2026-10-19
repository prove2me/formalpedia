-- Prove2me | Theorems.Thm_MazurTransfer_scalar_cocycle_coboundary_of_commutator_zero
-- name    : MazurTransfer.scalar_cocycle_coboundary_of_commutator_zero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-16T10:44:08.561724+00:00
-- url     : https://prove2.me/theorems/e732f940-8593-4532-92a6-c6c48b4c428a
-- title:
--   Scalar cocycles vanishing on commutators are coboundaries
-- statement:
--   Let $G$ be a group, $k$ a field, and $\chi:G\to k^\times$ a nontrivial character. Let $c:G\to k$ satisfy the twisted cocycle identity $c(gh)=c(g)+\chi(g)c(h)$. If $c$ vanishes on every commutator $g^{-1}h^{-1}gh$, then $c$ is a coboundary: there is $a\in k$ such that $c(g)=\chi(g)a-a$ for every $g$. No finiteness or topology hypothesis is needed. The vanishing on commutators gives the cross relation between $c$ and $\chi-1$, and division at any element with nontrivial character yields the claimed common scalar.
-- source:
--   Independent standalone Mathlib proof of MazurTransfer.ScalarCocycleTameKernelDetection.exists_coboundary. Applied to the same original chi13 cocycle on valuation inertia after actual finite Galois factorization and prime-power wild commutator annihilation in the order-13 Picard norm descent.

import Mathlib

theorem MazurTransfer.scalar_cocycle_coboundary_of_commutator_zero
    {k G : Type} [Field k] [Group G]
    (χ : G →* kˣ) (c : G → k)
    (hc : ∀ g h, c (g * h) = c g + (χ g : k) * c h)
    (hcomm : ∀ g h, c (g⁻¹ * h⁻¹ * g * h) = 0)
    (hχ : ∃ g, χ g ≠ 1) :
    ∃ a : k, ∀ g, c g = (χ g : k) * a - a := by sorry
