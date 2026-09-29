-- Prove2me | Theorems.Thm_HopfOrder_mem_of_forall_mem_dual_apply_mem_range
-- name    : HopfOrder.mem_of_forall_mem_dual_apply_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/f04a5def-fbb9-5dc4-943f-6c1620830f3f
-- title:
--   Integrality against the dual lattice forces membership
-- statement:
--   Let $R$ be a commutative domain that is a principal ideal ring, with field of fractions $K$, and let $A$ be a commutative ring carrying a Hopf algebra structure over $K$ that is finite-dimensional as a $K$-module and cocommutative as a $K$-coalgebra, together with an $R$-algebra structure compatible with that of $K$ (a scalar tower $R \to K \to A$); the Cartier dual $\mathrm{CartierDual}\ K\ A$, which by definition is the $K$-linear dual $\mathrm{Module.Dual}\ K\ A$ of $A$, is likewise equipped with an $R$-algebra structure compatible with the $K$-structure. Let $S$ be an $R$-subalgebra of $A$ that is finite as an $R$-module and whose $K$-span is all of $A$, and let $S'$ be an $R$-subalgebra of the Cartier dual characterised by the property that a functional $\varphi$ lies in $S'$ exactly when $\varphi(b)$ belongs to the image of $R$ in $K$ for every $b \in S$. Then any $a \in A$ with $\varphi(a)$ in the image of $R$ for all $\varphi \in S'$ already lies in $S$.
--
--   This is the non-trivial half of the biduality $S^{\vee\vee} = S$ for a full $R$-lattice $S$ in a finite-dimensional $K$-vector space, stated for an order inside a finite cocommutative Hopf algebra, the Hopf structure serving only to give meaning to the Cartier dual. It underlies the inclusion-reversing correspondence between orders of $A$ and of its Cartier dual, and is used in the construction of a least Hopf order, [`HopfOrder.exists_isLeast`](thm.html#HopfOrder.exists_isLeast).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_mem_of_forall_mem_dual_apply_mem_range.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem HopfOrder.mem_of_forall_mem_dual_apply_mem_range
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    [Module.Finite K A] [Coalgebra.IsCocomm K A]
    [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (S' : Subalgebra R (CartierDual K A))
    (hS' : ∀ φ : CartierDual K A, φ ∈ S' ↔ ∀ b ∈ S, φ b ∈ (algebraMap R K).range)
    (a : A) (ha : ∀ φ ∈ S', φ a ∈ (algebraMap R K).range) : a ∈ S := by sorry
