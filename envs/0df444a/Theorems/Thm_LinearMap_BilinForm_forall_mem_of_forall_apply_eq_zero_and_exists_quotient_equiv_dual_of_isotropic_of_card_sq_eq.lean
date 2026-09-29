-- Prove2me | Theorems.Thm_LinearMap_BilinForm_forall_mem_of_forall_apply_eq_zero_and_exists_quotient_equiv_dual_of_isotropic_of_card_sq_eq
-- name    : LinearMap.BilinForm.forall_mem_of_forall_apply_eq_zero_and_exists_quotient_equiv_dual_of_isotropic_of_card_sq_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/124a9bfa-0af5-5ea3-9c25-888f385a33bc
-- title:
--   Maximal isotropic subspace equals its orthogonal; V/A ≅ A^∨
-- statement:
--   Let $p$ be a prime, and let $V$ be a finite $\mathbb{F}_p$-vector space, i.e. an additive commutative group with a $\mathbb{Z}/p$-module structure whose underlying type is finite. Let $b$ be a $\mathbb{Z}/p$-bilinear form on $V$, assumed non-degenerate on both sides: if $b(x,y)=0$ for all $y$ then $x=0$, and if $b(x,y)=0$ for all $x$ then $y=0$. No symmetry or reflexivity is assumed. Let $A \leq V$ be a $\mathbb{Z}/p$-submodule which is totally isotropic, in the sense that $b(x,y)=0$ for all $x,y \in A$, and which satisfies the cardinality condition $(\#A)^2 = \#V$ (as natural-number cardinalities). The conclusion is a conjunction. First, $A$ contains its own right orthogonal: every $y \in V$ with $b(a,y)=0$ for all $a \in A$ lies in $A$. Second, there exists a $\mathbb{Z}/p$-linear isomorphism $\varphi$ from the quotient $V/A$ onto the dual $\operatorname{Hom}_{\mathbb{Z}/p}(A,\mathbb{Z}/p)$ such that for every $y \in V$ and every $a \in A$ one has $\varphi(y \bmod A)(a) = b(a,y)$.
--
--   This is the standard linear algebra of maximal isotropic (Lagrangian) subspaces for a non-degenerate pairing, with the half-dimension condition recorded multiplicatively as $(\#A)^2 = \#V$ so that a consumer may supply it from a counting argument. It is used in the analysis of the $p$-part of the torsion/component data attached to a modular curve, in [`ModularCurve.exists_linearMap_injective_range_eq_dual_multiplicativeSubmodule_ssPolarDifferentials_of_jHNeronObjectAtP_of_twoCompRegularDifferentials_of_ordinary_torusCoords_of_mem_infSubgroup`](thm.html#ModularCurve.exists_linearMap_injective_range_eq_dual_multiplicativeSubmodule_ssPolarDifferentials_of_jHNeronObjectAtP_of_twoCompRegularDifferentials_of_ordinary_torusCoords_of_mem_infSubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_BilinForm_forall_mem_of_forall_apply_eq_zero_and_exists_quotient_equiv_dual_of_isotropic_of_card_sq_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem LinearMap.BilinForm.forall_mem_of_forall_apply_eq_zero_and_exists_quotient_equiv_dual_of_isotropic_of_card_sq_eq
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (b : LinearMap.BilinForm (ZMod p) V)
    (hleft : ∀ x : V, (∀ y : V, b x y = 0) → x = 0) (hright : ∀ y : V, (∀ x : V, b x y = 0) → y = 0)
    (A : Submodule (ZMod p) V) (hiso : ∀ x ∈ A, ∀ y ∈ A, b x y = 0)
    (hcard : Nat.card A ^ 2 = Nat.card V) :
    (∀ y : V, (∀ a ∈ A, b a y = 0) → y ∈ A) ∧
    ∃ φ : (V ⧸ A) ≃ₗ[ZMod p] (A →ₗ[ZMod p] ZMod p),
      ∀ (y : V) (a : A), φ (Submodule.Quotient.mk y) a = b a y := by sorry
