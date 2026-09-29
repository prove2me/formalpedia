-- Prove2me | Theorems.Thm_FullLevelTate_Datum_isoHomGal_inertia_quadratic_of_specialization
-- name    : FullLevelTate.Datum.isoHomGal_inertia_quadratic_of_specialization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/17e2e7c3-9313-5dd3-9ffd-4fee845922a9
-- title:
--   Quadratic relation for inertia on cuspidal intertwiners
-- statement:
--   Fix a prime $q$, a natural number $M'$, a local ring $O'$ and a full-level-$q$ Tate datum $D$ over them (a finite free $O'$-module $D.V$ with commuting actions `gal` of $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$, `gl2` of $GL_2(\mathbb Z/q)$ and `hecke` of the Hecke algebra, adically continuous, unramified outside $qM'$ and satisfying the Eichler–Shimura relation). Let $K$ be a field that is an $O'$-algebra, $\theta:\mathbb F_{q^2}^{\times}\to K^{\times}$ a character, $W$ a finite-dimensional $K$-space and $\sigma$ a representation of $GL_2(\mathbb Z/q)$ on $W$ which is cuspidal of type $\theta$ (dimension $q-1$, no non-zero vector fixed by all unipotents, scalars acting trivially, and the prescribed torus characteristic-polynomial identity). Let $P$ be a valuation subring of $\overline{\mathbb Q}$, let $\pi\in\overline{\mathbb Q}$ satisfy $\pi^{q^2-1}=q$, and let $\iota:\mathbb F_{q^2}\to\kappa(P)$ be a ring homomorphism. Let $T$ be a $K$-module with a monoid homomorphism $\rho_T$ from the subgroup $H\le GL_2(\mathbb Z/q)\times\mathbb F_{q^2}^{\times}$ cut out by $\det(g)\,\alpha^{q+1}=1$ into $\operatorname{End}_K T$, subject to the hypothesis `hT`: whenever $u:W\to T$ is $K$-linear and satisfies $u\circ\sigma(g)=\rho_T(g,1)\circ u$ for all $(g,1)\in H$, then for all $(g,\alpha)\in H$ the operator $A(v)=\rho_T(g,\alpha)\circ v\circ\sigma(g^{-1})$ obeys $A(A u)-(\theta(\alpha)+\theta(\alpha^{q}))\,A u+\theta(\alpha)\theta(\alpha^{q})\,u=0$. Let $sp:K\otimes_{O'}D.V\to T$ be $K$-linear and such that for every $\tau$ in the inertia subgroup of $P$ over $\mathbb Q$, every $\alpha$ with $\iota(\alpha)$ equal to the tame character $\tau\pi/\pi \bmod P$, and every $(g,\alpha)\in H$, one has $sp\circ(D.\mathrm{gl2}(g)\,D.\mathrm{gal}(\tau))_K=\rho_T(g,\alpha)\circ sp$. Finally let $U$ be a $K$-submodule of the space of $f:W\to K\otimes_{O'}D.V$ intertwining $\sigma$ (restricted to the full subgroup $\top$) with the base-changed `gl2`-action, stable under $f\mapsto (D.\mathrm{gal}(\tau))_K\circ f$ for $\tau$ in that inertia subgroup, and such that $sp\circ f=0$ forces $f=0$ for $f\in U$. The conclusion: for every such $\tau$, every $\alpha$ with $\iota(\alpha)$ the tame character of $\tau$, and every $f\in U$, the identity $(D.\mathrm{gal}(\tau))_K^{2}\circ f-(\theta(\alpha)+\theta(\alpha^{q}))\,(D.\mathrm{gal}(\tau))_K\circ f+\theta(\alpha)\theta(\alpha^{q})\,f=0$ holds in $\operatorname{Hom}_K(W,K\otimes_{O'}D.V)$.
--
--   This transports a quadratic relation satisfied by the action of the pairs $(g,\alpha)$ on a Drinfeld-type module $T$ back, through an injective specialisation map, to the inertia action at $q$ on the $\theta$-typic intertwiners of a full-level Tate datum: inertia acts with characteristic polynomial $(X-\theta(\alpha))(X-\theta(\alpha^{q}))$. It feeds the determination of the inertia labels of a newform whose associated $GL_2(\mathbb Z/q)$-subrepresentation is cuspidal of type $\theta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_Datum_isoHomGal_inertia_quadratic_of_specialization.lean

import Definitions.Def_FullLevelTate_IsoHom
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_GaloisRep_TameCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.Datum.isoHomGal_inertia_quadratic_of_specialization
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (O' : Type) [CommRing O'] [IsLocalRing O']
    (D : FullLevelTate.Datum q M' O')
    (K : Type) [Field K] [Algebra O' K]
    (θ : (GaloisField q 2)ˣ →* Kˣ) {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (σ : Representation K (CuspidalType.GL2 q) W) (hσ : CuspidalType.IsCuspidalOfType θ σ)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P)
    (T : Type) [AddCommGroup T] [Module K T] (ρT : ↥(DrinfeldCurve.hSubgroup q) →* Module.End K T)
    (hT : ∀ u : W →ₗ[K] T,
      (∀ (g : CuspidalType.GL2 q) (hg₁ : (g, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
        u ∘ₗ σ g = ρT ⟨(g, 1), hg₁⟩ ∘ₗ u) →
      ∀ (α : (GaloisField q 2)ˣ) (g : CuspidalType.GL2 q) (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
        let A : (W →ₗ[K] T) → (W →ₗ[K] T) := fun v => ρT ⟨(g, α), hg⟩ ∘ₗ v ∘ₗ σ g⁻¹
        A (A u) - (((θ α : Kˣ) : K) + ((θ (α ^ q) : Kˣ) : K)) • A u +
          (((θ α : Kˣ) : K) * ((θ (α ^ q) : Kˣ) : K)) • u = 0)
    (sp : K ⊗[O'] D.V →ₗ[K] T)
    (hsp : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
      ι (α : GaloisField q 2) = P.tameCharacter π τ →
        ∀ (g : CuspidalType.GL2 q) (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
          sp ∘ₗ ((D.gl2 g * D.gal τ).baseChange K) = ρT ⟨(g, α), hg⟩ ∘ₗ sp)
    (U : Submodule K ↥(D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype)))
    (hU : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ U,
      D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ f ∈ U)
    (hinj : ∀ f ∈ U,
      sp ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) = 0 → f = 0) :
    ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
      ι (α : GaloisField q 2) = P.tameCharacter π τ →
        ∀ f ∈ U,
          ((D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ
                (D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ f) :
                ↥(D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype))) :
              W →ₗ[K] K ⊗[O'] D.V) -
            (((θ α : Kˣ) : K) + ((θ (α ^ q) : Kˣ) : K)) •
              ((D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ f :
                  ↥(D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype))) :
                W →ₗ[K] K ⊗[O'] D.V) +
            (((θ α : Kˣ) : K) * ((θ (α ^ q) : Kˣ) : K)) •
              ((f : ↥(D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype))) :
                W →ₗ[K] K ⊗[O'] D.V) = 0 := by sorry
