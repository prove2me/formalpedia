-- Prove2me | Theorems.Thm_Module_IsDirectLimit_exists_linearEquiv_of_finitePresentation
-- name    : Module.IsDirectLimit.exists_linearEquiv_of_finitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/b47881fb-4fd5-5133-a2bb-e6115b57feac
-- title:
--   Isomorphisms of finitely presented modules descend to a stage
-- statement:
--   Let $\iota$ be a nonempty directed preorder, $B_0$ a commutative ring, and $(B_i)_{i\in\iota}$ a family of commutative $B_0$-algebras equipped with $B_0$-algebra transition maps $\tau_{ij}\colon B_i\to B_j$ for $i\le j$ forming a directed system (so $\tau_{ii}=\mathrm{id}$ and $\tau_{jk}\circ\tau_{ij}=\tau_{ik}$). Let $B_\omega$ be a commutative $B_0$-algebra with $B_0$-algebra maps $g_i\colon B_i\to B_\omega$ satisfying $g_j\circ\tau_{ij}=g_i$ for $i\le j$, and assume $B_\omega$ is the colimit elementwise: every $b\in B_\omega$ is of the form $g_i(x)$ for some $i$ and $x\in B_i$, and whenever $g_i(x)=0$ there is $j\ge i$ with $\tau_{ij}(x)=0$. Let $P$ and $Q$ be finitely presented $B_0$-modules, and let $e\colon B_\omega\otimes_{B_0}P\to B_\omega\otimes_{B_0}Q$ be a $B_\omega$-linear isomorphism. Then there exist an index $i$ and a $B_i$-linear isomorphism $e_i\colon B_i\otimes_{B_0}P\to B_i\otimes_{B_0}Q$ inducing $e$, in the sense that the square of $B_0$-linear maps commutes: $e\circ(g_i\otimes 1_P)=(g_i\otimes 1_Q)\circ e_i$ as maps $B_i\otimes_{B_0}P\to B_\omega\otimes_{B_0}Q$, where $g_i\otimes 1$ denotes the base-change map induced by $g_i$.
--
--   This is the descent of isomorphisms between base changes of finitely presented modules along a filtered colimit of rings (EGA IV 8.5.2), with the colimit hypothesis expressed elementwise rather than through a quotient construction. It is used in the construction of the relative Picard presheaf, in [`AlgebraicGeometry.RelPicard.isLFPInj_relPicardPresheaf`](thm.html#AlgebraicGeometry.RelPicard.isLFPInj_relPicardPresheaf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_IsDirectLimit_exists_linearEquiv_of_finitePresentation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem Module.IsDirectLimit.exists_linearEquiv_of_finitePresentation
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {B₀ : Type u} [CommRing B₀]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra B₀ (B i)]
    (τ : ∀ i j, i ≤ j → B i →ₐ[B₀] B j) [DirectedSystem B (fun i j h => τ i j h)]
    (Bω : Type u) [CommRing Bω] [Algebra B₀ Bω] (g : ∀ i, B i →ₐ[B₀] Bω)
    (hg : ∀ i j (h : i ≤ j), (g j).comp (τ i j h) = g i)
    (hsurj : ∀ b : Bω, ∃ i x, g i x = b)
    (hzero : ∀ i (x : B i), g i x = 0 → ∃ (j : ι) (h : i ≤ j), τ i j h x = 0)
    (P Q : Type w) [AddCommGroup P] [Module B₀ P] [AddCommGroup Q] [Module B₀ Q]
    [Module.FinitePresentation B₀ P] [Module.FinitePresentation B₀ Q]
    (e : TensorProduct B₀ Bω P ≃ₗ[Bω] TensorProduct B₀ Bω Q) :
    ∃ (i : ι) (eᵢ : TensorProduct B₀ (B i) P ≃ₗ[B i] TensorProduct B₀ (B i) Q),
      (e : _ →ₗ[Bω] _).restrictScalars B₀ ∘ₗ (g i).toLinearMap.rTensor P =
        (g i).toLinearMap.rTensor Q ∘ₗ (eᵢ : _ →ₗ[B i] _).restrictScalars B₀ := by sorry
