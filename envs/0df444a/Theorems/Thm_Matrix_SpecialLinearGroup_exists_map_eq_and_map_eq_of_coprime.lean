-- Prove2me | Theorems.Thm_Matrix_SpecialLinearGroup_exists_map_eq_and_map_eq_of_coprime
-- name    : Matrix.SpecialLinearGroup.exists_map_eq_and_map_eq_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/fd8afdfc-57a8-5eeb-b4f8-3534ddf43d8b
-- title:
--   Simultaneous lift to SL₂(ℤ) for coprime moduli
-- statement:
--   Let $m$ and $M$ be natural numbers, both nonzero, with $\gcd(m,M)=1$, and let $A \in SL(2,\mathbb{Z}/m)$ and $B \in SL(2,\mathbb{Z}/M)$ be prescribed special linear matrices over the respective residue rings. The assertion is that there exists $\gamma \in SL(2,\mathbb{Z})$ whose entrywise reduction along the canonical ring homomorphism $\mathbb{Z} \to \mathbb{Z}/m$, taken as a map of special linear groups, equals $A$, and whose entrywise reduction along $\mathbb{Z} \to \mathbb{Z}/M$ equals $B$; that is, $\gamma \equiv A \pmod m$ and $\gamma \equiv B \pmod M$ as elements of $SL(2,\mathbb{Z}/m)$ and $SL(2,\mathbb{Z}/M)$. Here the reduction maps are `Matrix.SpecialLinearGroup.map` applied to `Int.castRingHom`, so the equalities are equalities of group elements, not merely of underlying matrices up to sign.
--
--   This is the standard simultaneous approximation statement for $SL_2$ over $\mathbb{Z}$ with respect to two coprime moduli, the group-theoretic form of the Chinese remainder theorem combined with surjectivity of reduction. It is used for the matrix bookkeeping of congruence subgroups and of level structures on modular curves, in particular by results producing elements of $\Gamma(N)$ or $\Gamma_0(N)$ with prescribed behaviour at an auxiliary coprime level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_SpecialLinearGroup_exists_map_eq_and_map_eq_of_coprime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem Matrix.SpecialLinearGroup.exists_map_eq_and_map_eq_of_coprime
    (m M : ℕ) [NeZero m] [NeZero M] (hmM : Nat.Coprime m M)
    (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) :
    ∃ γ : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) γ = A ∧
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = B := by sorry
