-- Prove2me | Theorems.Thm_Module_IsDirectLimit_exists_stage_linearEquiv_of_finitePresentation_compat
-- name    : Module.IsDirectLimit.exists_stage_linearEquiv_of_finitePresentation_compat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/202e84fd-b14a-53bf-824a-bf98493e0b39
-- title:
--   Descent of isomorphisms of finitely presented modules to a stage
-- statement:
--   Let $\iota$ be a nonempty directed preorder, $B_0$ a commutative ring, and $(B_i)_{i\in\iota}$ a family of commutative $B_0$-algebras equipped with $B_0$-algebra transition maps $\tau_{ij}\colon B_i\to B_j$ for $i\le j$ forming a directed system. Let $B_\omega$ be a commutative $B_0$-algebra with $B_0$-algebra maps $g_i\colon B_i\to B_\omega$ such that $g_j\circ\tau_{ij}=g_i$ for all $i\le j$, such that every element of $B_\omega$ is of the form $g_i(x)$ for some $i$ and some $x\in B_i$, and such that $g_i(x)=0$ implies $\tau_{ij}(x)=0$ for some $j\ge i$; thus the $g_i$ exhibit $B_\omega$ as the direct limit of the system elementwise. Fix a stage $i_0$ and an algebra structure of $B_\omega$ over $B_{i_0}$ whose structure map agrees pointwise with $g_{i_0}$, and let $P,Q$ be finitely presented $B_{i_0}$-modules together with a $B_\omega$-linear isomorphism $e\colon B_\omega\otimes_{B_{i_0}}P\xrightarrow{\ \sim\ }B_\omega\otimes_{B_{i_0}}Q$. The conclusion asserts the existence of $j\ge i_0$, of a $B_{i_0}$-algebra map $g_j'\colon B_j\to B_\omega$ agreeing pointwise with $g_j$ (where $B_j$ is a $B_{i_0}$-algebra via $\tau_{i_0 j}$), and of a $B_j$-linear isomorphism $e_j\colon B_j\otimes_{B_{i_0}}P\xrightarrow{\ \sim\ }B_j\otimes_{B_{i_0}}Q$, such that $e\bigl((g_j'\otimes\mathrm{id}_P)(x)\bigr)=(g_j'\otimes\mathrm{id}_Q)(e_j(x))$ for every $x\in B_j\otimes_{B_{i_0}}P$, i.e. $e_j$ induces $e$ after base change along $g_j'$.
--
--   This is the standard descent statement that an isomorphism of base changes of finitely presented modules to a direct limit ring already comes from some finite stage, here in the form that records the commuting square relating the stage isomorphism to the given one. It is used in the construction of relative Picard data, where the compatibility square is needed to transport an isomorphism found over the limit back to a finitely generated subalgebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_IsDirectLimit_exists_stage_linearEquiv_of_finitePresentation_compat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem Module.IsDirectLimit.exists_stage_linearEquiv_of_finitePresentation_compat
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {B₀ : Type u} [CommRing B₀]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra B₀ (B i)]
    (τ : ∀ i j, i ≤ j → B i →ₐ[B₀] B j) [DirectedSystem B (fun i j h => τ i j h)]
    (Bω : Type u) [CommRing Bω] [Algebra B₀ Bω] (g : ∀ i, B i →ₐ[B₀] Bω)
    (hg : ∀ i j (h : i ≤ j), (g j).comp (τ i j h) = g i)
    (hsurj : ∀ b : Bω, ∃ i x, g i x = b)
    (hzero : ∀ i (x : B i), g i x = 0 → ∃ (j : ι) (h : i ≤ j), τ i j h x = 0)
    (i₀ : ι) [Algebra (B i₀) Bω] (hgi : ∀ x, algebraMap (B i₀) Bω x = g i₀ x)
    (P Q : Type w) [AddCommGroup P] [Module (B i₀) P] [AddCommGroup Q] [Module (B i₀) Q]
    [Module.FinitePresentation (B i₀) P] [Module.FinitePresentation (B i₀) Q]
    (e : TensorProduct (B i₀) Bω P ≃ₗ[Bω] TensorProduct (B i₀) Bω Q) :
    ∃ (j : ι) (hj : i₀ ≤ j) (gj : letI := (τ i₀ j hj).toRingHom.toAlgebra; B j →ₐ[B i₀] Bω) (_ : ∀ b, gj b = g j b)
      (ej : letI := (τ i₀ j hj).toRingHom.toAlgebra; TensorProduct (B i₀) (B j) P ≃ₗ[B j] TensorProduct (B i₀) (B j) Q),
      letI := (τ i₀ j hj).toRingHom.toAlgebra
      ∀ x : TensorProduct (B i₀) (B j) P, e (gj.toLinearMap.rTensor P x) = gj.toLinearMap.rTensor Q (ej x) := by sorry
