-- Prove2me | Theorems.Thm_NeronModelInfra_exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem
-- name    : NeronModelInfra.exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/52e9a52e-7b19-5850-aaf7-bb1d0d271900
-- title:
--   Dense slices near a maximal point of the special fibre
-- statement:
--   Let $R$ be a noetherian local commutative ring with closed point $s =$ `IsLocalRing.closedPoint R`, let $X$ be a scheme and $f \colon X \to \operatorname{Spec} R$ a morphism that is locally of finite type and quasi-compact. Let $Z$ be an open subset of the scheme $X \times_{\operatorname{Spec} R} X$ (the categorical pullback of $f$ with itself) and assume that $Z$ contains every maximal point of the special fibre of the first projection composed with $f$: that is, every point $p$ of $X \times_R X$ with $f(\mathrm{pr}_1(p)) = s$ such that any $y$ with $f(\mathrm{pr}_1(y)) = s$ which specialises to $p$ equals $p$, lies in $Z$. Let $\xi \in X$ satisfy $f(\xi) = s$ and be maximal among such points, i.e. every $y \in X$ with $f(y) = s$ specialising to $\xi$ equals $\xi$. The conclusion is that there exists an open subset $N \subseteq X$ containing $\xi$ such that for every $a \in N$ with $f(a) = s$, the preimage of $Z$ under the inclusion of the subspace $\{q \in X \times_R X : \mathrm{pr}_1(q) = a\}$ into $X \times_R X$ is dense in that subspace.
--
--   This is the topological step underlying the passage from a birational group law to a group law on a dense open part (Bosch–Lütkebohmert–Raynaud 5.2, Proposition 2), resting on the constructibility of the locus of non-dense slices as in EGA IV 9.5.3: over a maximal point of $X_k$ the maximal points of a $\mathrm{pr}_1$-slice are maximal points of the special fibre of $X \times_R X$, hence lie in $Z$. It is used in the Néron model infrastructure, in [`NeronModelInfra.exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul`](thm.html#NeronModelInfra.exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem NeronModelInfra.exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : (pullback f f).Opens)
    (hZ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Z)
    (ξ : X) (hξ : f.base ξ = IsLocalRing.closedPoint R)
    (hξmax : ∀ y : X, y ⤳ ξ → f.base y = IsLocalRing.closedPoint R → y = ξ) :
    ∃ N : X.Opens, ξ ∈ N ∧ ∀ a : X, a ∈ N → f.base a = IsLocalRing.closedPoint R →
      Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = a} → ↑(pullback f f)) ⁻¹'
        (Z : Set ↑(pullback f f))) := by sorry
