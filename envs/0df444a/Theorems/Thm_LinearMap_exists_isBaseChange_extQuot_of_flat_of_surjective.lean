-- Prove2me | Theorems.Thm_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective
-- name    : LinearMap.exists_isBaseChange_extQuot_of_flat_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/560f71be-285a-5a54-ac0f-84686639b31d
-- title:
--   Flat base change of the Ext¹-quotient of a presentation
-- statement:
--   Let $B$ be a Noetherian commutative ring and $B'$ a commutative $B$-algebra which is flat as a $B$-module. Let $M$, $N$ be $B$-modules and let $M'$, $N'$ carry compatible $B$- and $B'$-module structures (scalar towers over $B \to B'$). Let $\mu : M \to M'$ and $\nu : N \to N'$ be $B$-linear maps exhibiting $M'$ and $N'$ as the base changes of $M$ and $N$ along $B \to B'$ (`IsBaseChange B' μ`, `IsBaseChange B' ν`). Let $r$ be a natural number, $p : B^r \to M$ a surjective $B$-linear map, and $p' : (B')^r \to M'$ a $B'$-linear map such that $p'$ applied to the image under $\mathrm{algebraMap}$ of a vector $v \in B^r$ equals $\mu(p\,v)$. Write $S = \ker p$ and $S' = \ker p'$, and form the two quotients $E = \operatorname{Hom}_B(S,N)/\mathrm{im}\bigl(\operatorname{Hom}_B(B^r,N) \to \operatorname{Hom}_B(S,N)\bigr)$ and $E' = \operatorname{Hom}_{B'}(S',N')/\mathrm{im}\bigl(\operatorname{Hom}_{B'}((B')^r,N') \to \operatorname{Hom}_{B'}(S',N')\bigr)$, the maps being restriction along the inclusions of the kernels. The conclusion asserts: $p'$ is surjective; and there exist a $B$-linear map $g : S \to S'$ and a $B$-linear map $T : E \to E'$ such that $g$ acts coordinatewise by $\mathrm{algebraMap}\ B\ B'$ on the coordinates of elements of $S \subseteq B^r$; $T$ exhibits $E'$ as the base change of $E$ along $B \to B'$ (`IsBaseChange B' T`); every $B$-linear $\delta : S \to N$ admits a $B'$-linear $\delta' : S' \to N'$ with $\delta' \circ g = \nu \circ \delta$; and for any such pair $(\delta,\delta')$ one has $T[\delta] = [\delta']$ on classes.
--
--   This is flat base change for the $\mathrm{Ext}^1$-quotient attached to a finite free presentation: the groups $E$ and $E'$ are the usual $\operatorname{Ext}^1_B(M,N)$ and $\operatorname{Ext}^1_{B'}(M',N')$ computed from the presentation $B^r \to M$ and its base change, and the statement records not only the isomorphism $E \otimes_B B' \cong E'$ but also its effect on representing homomorphisms $\delta$. It is used in the construction of coherent data for presheaves of modules, via [`AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_extQuot_of_isCoherent`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_extQuot_of_isCoherent), where the comparison must be known on representatives in order to glue over a basis of opens.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem LinearMap.exists_isBaseChange_extQuot_of_flat_of_surjective
    {B : Type u} [CommRing B] [IsNoetherianRing B] {B' : Type u} [CommRing B'] [Algebra B B'] [Module.Flat B B']
    {M : Type v} [AddCommGroup M] [Module B M] {N : Type v} [AddCommGroup N] [Module B N]
    {M' : Type v} [AddCommGroup M'] [Module B M'] [Module B' M'] [IsScalarTower B B' M']
    {N' : Type v} [AddCommGroup N'] [Module B N'] [Module B' N'] [IsScalarTower B B' N']
    (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    (p' : (Fin r → B') →ₗ[B'] M') (hp' : ∀ v : Fin r → B, p' (fun i => algebraMap B B' (v i)) = μ (p v)) :
    Function.Surjective p' ∧
    ∃ (g : ↥(LinearMap.ker p) →ₗ[B] ↥(LinearMap.ker p'))
      (T : ((↥(LinearMap.ker p) →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N (LinearMap.ker p).subtype)) →ₗ[B]
           ((↥(LinearMap.ker p') →ₗ[B'] N') ⧸ LinearMap.range (LinearMap.lcomp B' N' (LinearMap.ker p').subtype))),
      (∀ (s : ↥(LinearMap.ker p)) (i : Fin r), ((g s : ↥(LinearMap.ker p')) : Fin r → B') i = algebraMap B B' ((s : Fin r → B) i)) ∧
      IsBaseChange B' T ∧
      (∀ δ : ↥(LinearMap.ker p) →ₗ[B] N, ∃ δ' : ↥(LinearMap.ker p') →ₗ[B'] N', ∀ s : ↥(LinearMap.ker p), δ' (g s) = ν (δ s)) ∧
      (∀ (δ : ↥(LinearMap.ker p) →ₗ[B] N) (δ' : ↥(LinearMap.ker p') →ₗ[B'] N'),
        (∀ s : ↥(LinearMap.ker p), δ' (g s) = ν (δ s)) →
        T (Submodule.Quotient.mk δ) = Submodule.Quotient.mk δ') := by sorry
