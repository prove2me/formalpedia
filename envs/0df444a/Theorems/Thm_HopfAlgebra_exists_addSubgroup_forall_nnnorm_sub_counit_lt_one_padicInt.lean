-- Prove2me | Theorems.Thm_HopfAlgebra_exists_addSubgroup_forall_nnnorm_sub_counit_lt_one_padicInt
-- name    : HopfAlgebra.exists_addSubgroup_forall_nnnorm_sub_counit_lt_one_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/ce0315a3-ce52-5df9-82e6-776c2fa169dd
-- title:
--   Identity-reducing points form a Galois-stable subgroup containing inertia displacements
-- statement:
--   Fix a prime $p$, and let $H$ be a commutative ring equipped with a Hopf algebra structure over $\mathbb{Z}_p$ that is module-finite and flat over $\mathbb{Z}_p$ and whose comultiplication is cocommutative. Let $M$ be an additive commutative group and let $e$ be a bijection from `WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)`, the set of $\mathbb{Z}_p$-algebra homomorphisms $H \to$ `PadicAlgCl p` with the convolution product, onto $M$ carrying that product to addition: $e(f\cdot g)=e(f)+e(g)$. Let $\mathrm{act}$ assign to each $\mathbb{Q}_p$-algebra automorphism $\sigma$ of `PadicAlgCl p` a map $M \to M$, compatibly with $e$: whenever $f,g$ are such homomorphisms with $g(h)=\sigma(f(h))$ for all $h \in H$, one has $e(g)=\mathrm{act}\,\sigma\,(e(f))$. Then there is an additive subgroup $K \le M$ with the following three properties. First, $x \in K$ if and only if $x=e(f)$ for some $f$ satisfying $\|f(h)-\varepsilon(h)\|_{+}<1$ for every $h \in H$, where $\varepsilon$ is the counit of $H$ composed with the structure map $\mathbb{Z}_p \to$ `PadicAlgCl p`. Secondly, $\mathrm{act}\,\sigma$ maps $K$ into $K$ for every such $\sigma$. Thirdly, if $\sigma$ lies in the image in the full automorphism group of the inertia subgroup of the decomposition subgroup over $\mathbb{Q}_p$ of the valuation subring [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) of `PadicAlgCl p`, then $\mathrm{act}\,\sigma\,(x)-x \in K$ for all $x \in M$.
--
--   For $G=\operatorname{Spec} H$ a finite flat commutative group scheme over $\mathbb{Z}_p$, the subgroup $K$ is the group of points of $G$ over `PadicAlgCl p` that reduce to the identity, transported through the chosen identification $e$ of the point group with $M$; the third clause records that inertia acts trivially modulo the maximal ideal of the valuation ring, so every inertia displacement is identity-reducing. It is used by [`HopfAlgebra.act_eq_self_of_inertiaTrivialChain_padicInt`](thm.html#HopfAlgebra.act_eq_self_of_inertiaTrivialChain_padicInt) and [`HopfAlgebra.inertia_displacement_eq_nsmul_of_inertiaTrivialOrCyclotomicChain_padicInt`](thm.html#HopfAlgebra.inertia_displacement_eq_nsmul_of_inertiaTrivialOrCyclotomicChain_padicInt) in the local analysis of inertia at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_addSubgroup_forall_nnnorm_sub_counit_lt_one_padicInt.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.exists_addSubgroup_forall_nnnorm_sub_counit_lt_one_padicInt
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (M : Type) [AddCommGroup M]
    (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M) (he : ∀ f g, e (f * g) = e f + e g)
    (act : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → M → M)
    (hact : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ h : H, g h = σ (f h)) → e g = act σ (e f)) :
    ∃ K : AddSubgroup M,
      (∀ x : M, x ∈ K ↔ ∃ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), e f = x ∧
        ∀ h : H, ‖f h - algebraMap ℤ_[p] (PadicAlgCl p) (Coalgebra.counit (R := ℤ_[p]) h)‖₊ < 1) ∧
      (∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : M), x ∈ K → act σ x ∈ K) ∧
      (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ x : M, act σ x - x ∈ K) := by sorry
