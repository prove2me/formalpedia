-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_ordinaryLine_baseChangeAlong
-- name    : GaloisRepAdic.exists_ordinaryLine_baseChangeAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/fb5db2cd-6583-523b-8695-6423399783ed
-- title:
--   Base change of an ordinary line along a local homomorphism
-- statement:
--   Let $A$ and $B$ be commutative local rings and let $\varphi : A \to B$ be a ring homomorphism which is local (non-units go to non-units). Let $\rho$ be an object of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16): a free, finite $A$-module $V$ with $\operatorname{rank}_A V = 2$, together with a monoid homomorphism $\rho.\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (realised as the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`) to $\mathrm{End}_A(V)$, satisfying the adic continuity condition. Let $P$ be a valuation subring of $\overline{\mathbb Q}$, with decomposition subgroup $D_P$ and with $I_P$ the image in the full Galois group of the inertia subgroup of $D_P$. Let $L \subseteq V$ be an $A$-submodule which is the span $A \cdot b_0$ of the first vector of some $A$-basis $(b_0,b_1)$ of $V$, such that $\rho(\sigma) L \subseteq L$ for all $\sigma \in D_P$ and $\rho(\sigma)v - v \in L$ for all $\sigma \in I_P$ and all $v \in V$. Then there is a $B$-submodule $L'$ of the base-changed representation $\rho.\mathrm{baseChangeAlong}\,\varphi$, whose underlying module is $B \otimes_A V$ with $\sigma$ acting by the base change of $\rho(\sigma)$, such that: $L'$ is the span of the first vector of some $B$-basis of $B \otimes_A V$; $L'$ is stable under all $\sigma \in D_P$; $\sigma v - v \in L'$ for all $\sigma \in I_P$ and all $v \in B \otimes_A V$; for $\sigma \in D_P$ and $z \in A$, if $\rho(\sigma)v - z v \in L$ for all $v \in V$ then $\sigma v' - \varphi(z) v' \in L'$ for all $v' \in B \otimes_A V$; and conversely, for $\sigma \in D_P$ and $z' \in B$, if $\sigma v' - z' v' \in L'$ for all $v' \in B \otimes_A V$ then $z' = \varphi(z)$ for some $z \in A$ with $\rho(\sigma)v - zv \in L$ for all $v \in V$.
--
--   This is the change of coefficient ring for the ordinary (Selmer) deformation condition at a place, in the form that remembers the stable line and records that the scalar by which a decomposition-group element acts on the quotient transforms along $\varphi$ in both directions. It is used in the passage from a Selmer-ordinary representation to the strict condition, where one must compare the line over $A$ with its image over a quotient or extension of $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_ordinaryLine_baseChangeAlong.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.exists_ordinaryLine_baseChangeAlong
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (L : Submodule A ρ.V) (hLb : ∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L) :
    ∃ L' : Submodule B (ρ.baseChangeAlong φ hφ).V,
      (∃ b' : Module.Basis (Fin 2) B (ρ.baseChangeAlong φ hφ).V, L' = B ∙ b' 0) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L', (ρ.baseChangeAlong φ hφ).ρ σ v ∈ L') ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : (ρ.baseChangeAlong φ hφ).V,
        (ρ.baseChangeAlong φ hφ).ρ σ v - v ∈ L') ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ z : A, (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) →
        ∀ v : (ρ.baseChangeAlong φ hφ).V, (ρ.baseChangeAlong φ hφ).ρ σ v - φ z • v ∈ L') ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ z' : B,
        (∀ v : (ρ.baseChangeAlong φ hφ).V, (ρ.baseChangeAlong φ hφ).ρ σ v - z' • v ∈ L') →
        ∃ z : A, (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) ∧ φ z = z') := by sorry
