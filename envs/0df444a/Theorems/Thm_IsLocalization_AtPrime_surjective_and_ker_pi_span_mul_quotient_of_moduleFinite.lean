-- Prove2me | Theorems.Thm_IsLocalization_AtPrime_surjective_and_ker_pi_span_mul_quotient_of_moduleFinite
-- name    : IsLocalization.AtPrime.surjective_and_ker_pi_span_mul_quotient_of_moduleFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/0518ebee-1f3d-5f4d-9aa5-81916d9fa57a
-- title:
--   Global-to-local map for a finite over-ring in K
-- statement:
--   Let $k$ be a field, $A$ a Noetherian domain which is a $k$-algebra, and $K$ a field which is a $k$-algebra and an $A$-algebra compatibly, and is the fraction field of $A$; assume every non-zero prime of $A$ is maximal and, for every maximal ideal $m$, the map $k \to A/m$ is surjective. Let $X$ be a type with a predicate $P$, and let $R$ assign to each $z : X$ a commutative ring with a $K$-algebra structure; for each $z$ satisfying $P$ assume in addition an $A$-algebra structure on $R z$ compatible with $K$, a maximal ideal $\mathfrak m_z$ of $A$, the assignment $z \mapsto \mathfrak m_z$ being injective, and that $R z$ is a localisation of $A$ at $\mathfrak m_z$. Let $B$ be an $A$-subalgebra of $K$ which is finite as an $A$-module. Put $B_z := \operatorname{span}_k\big(B \cdot \operatorname{im}(R z \to K)\big)$ and $Q_z := B_z / \big(\operatorname{span}_k \operatorname{im}(R z \to K) \cap B_z\big)$. Then the $k$-linear map $\varphi$ from $\operatorname{span}_k B$ to $\prod_{z : P} Q_z$, whose $z$-component is the inclusion $\operatorname{span}_k B \subseteq B_z$ followed by the quotient map, is surjective; its kernel is the intersection of $\operatorname{span}_k B$ with $\bigcap_z \operatorname{span}_k \operatorname{im}(R z \to K)$; only finitely many $Q_z$ are non-trivial; and each $Q_z$ is finite-dimensional over $k$.
--
--   This is the commutative-algebra core of a global-to-local statement for a one-dimensional Noetherian domain with residue fields equal to $k$: a finite over-ring $B \subseteq K$ surjects onto the product of the local quotients $B \cdot A_{\mathfrak m_z} / A_{\mathfrak m_z}$, with finite support and finite-dimensional factors. It is used by [`AlgebraicCurve.surjective_and_ker_pi_span_mul_quotient_of_finite`](thm.html#AlgebraicCurve.surjective_and_ker_pi_span_mul_quotient_of_finite), where $A$ is a ring of functions on an affine open of a curve and the $R z$ are the local rings at closed points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalization_AtPrime_surjective_and_ker_pi_span_mul_quotient_of_moduleFinite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped Pointwise

theorem IsLocalization.AtPrime.surjective_and_ker_pi_span_mul_quotient_of_moduleFinite
    (k : Type u) [Field k] {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Algebra k A]
    (K : Type u) [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K]
    (hdim : ∀ p : Ideal A, p.IsPrime → p ≠ ⊥ → p.IsMaximal)
    (hres : ∀ m : Ideal A, m.IsMaximal → Function.Surjective (algebraMap k (A ⧸ m)))
    {X : Type u} (P : X → Prop) (R : X → Type u) [∀ z, CommRing (R z)] [∀ z, Algebra (R z) K]
    [∀ z : {z : X // P z}, Algebra A (R z.1)] [∀ z : {z : X // P z}, IsScalarTower A (R z.1) K]
    (𝔪 : {z : X // P z} → Ideal A) [∀ z, (𝔪 z).IsMaximal] (h𝔪 : Function.Injective 𝔪)
    [∀ z : {z : X // P z}, IsLocalization.AtPrime (R z.1) (𝔪 z)]
    (B : Subalgebra A K) (hB : Module.Finite A B) :

    let Bz : X → Submodule k K := fun z =>
      Submodule.span k ((B : Set K) * Set.range (algebraMap (R z) K))
    let Q : X → Type u := fun z =>
      ↥(Bz z) ⧸ (Submodule.span k (Set.range (algebraMap (R z) K))).comap (Bz z).subtype

    let φ : ↥(Submodule.span k (B : Set K)) →ₗ[k] ((z : {z : X // P z}) → Q z.1) :=
      LinearMap.pi fun z => (Submodule.mkQ _).comp (Submodule.inclusion (Submodule.span_mono
        (fun b hb => Set.mem_mul.mpr ⟨b, hb, 1, ⟨1, map_one _⟩, mul_one b⟩)))
    Function.Surjective φ ∧
      LinearMap.ker φ = (⨅ z : {z : X // P z}, Submodule.span k (Set.range (algebraMap (R z.1) K))).comap
        (Submodule.span k (B : Set K)).subtype ∧
      {z : {z : X // P z} | Nontrivial (Q z.1)}.Finite ∧
      ∀ z : {z : X // P z}, FiniteDimensional k (Q z.1) := by sorry
