-- Prove2me | Theorems.Thm_ModularGroup_exists_apply_eq_sub_of_apply_neg_eq
-- name    : ModularGroup.exists_apply_eq_sub_of_apply_neg_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/fe14e759-fb0b-51f7-933e-972835e7b4ba
-- title:
--   Even functions on SL₂(ℤ) as coboundaries on Serre's tree
-- statement:
--   Let $A$ be an additive abelian group and let $c \colon \mathrm{SL}_2(\mathbb{Z}) \to A$ be any function which is even, in the sense that $c(-g) = c(g)$ for every $g \in \mathrm{SL}_2(\mathbb{Z})$ (the matrix group here being `SL(2, ℤ)`, i.e. $2\times 2$ integral matrices of determinant one). The assertion is the existence of two functions $a, b \colon \mathrm{SL}_2(\mathbb{Z}) \to A$ with the following three properties: $a$ is invariant under left multiplication by the matrix `ModularGroup.S`, that is $a(Sg) = a(g)$ for all $g$; $b$ is invariant under left multiplication by the product `ModularGroup.S * ModularGroup.T`, that is $b(STg) = b(g)$ for all $g$; and $c$ is the difference of the two, $c(g) = b(g) - a(g)$ for all $g \in \mathrm{SL}_2(\mathbb{Z})$. No further condition is imposed on $a$ and $b$, and no continuity, cocycle or finiteness hypothesis is placed on $c$ beyond evenness.
--
--   This is the cochain form of Serre's description of $\mathrm{SL}_2(\mathbb{Z})$ as an amalgam $\mathbb{Z}/4 *_{\mathbb{Z}/2} \mathbb{Z}/6$ acting on a tree: even functions on $\mathrm{SL}_2(\mathbb{Z})$ are the $1$-cochains of the tree whose vertices are the cosets $\langle S\rangle g$ and $\langle ST\rangle g$ and whose edges are the pairs $\{\pm g\}$, and the statement says that every such $1$-cochain is a coboundary. It is used in the construction of the cup-product pairing on modular curves, being cited by [`ModularCurve.CupPairing.exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero`](thm.html#ModularCurve.CupPairing.exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero) and [`ModularCurve.CupPairing.mult_mul_pair_eq_neg_finsum`](thm.html#ModularCurve.CupPairing.mult_mul_pair_eq_neg_finsum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularGroup_exists_apply_eq_sub_of_apply_neg_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularGroup.exists_apply_eq_sub_of_apply_neg_eq {A : Type*} [AddCommGroup A]
    (c : SL(2, ℤ) → A) (hc : ∀ g, c (-g) = c g) :
    ∃ a b : SL(2, ℤ) → A, (∀ g, a (ModularGroup.S * g) = a g) ∧
      (∀ g, b (ModularGroup.S * ModularGroup.T * g) = b g) ∧ ∀ g, c g = b g - a g := by sorry
