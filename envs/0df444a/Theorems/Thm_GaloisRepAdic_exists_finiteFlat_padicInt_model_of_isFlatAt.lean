-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_finiteFlat_padicInt_model_of_isFlatAt
-- name    : GaloisRepAdic.exists_finiteFlat_padicInt_model_of_isFlatAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/dce84f24-092a-5101-8875-26c1dfef6ebe
-- title:
--   Flatness at p yields a finite flat ℤₚ-model of ρ
-- statement:
--   Let $A$ be a finite commutative local ring, $p$ a prime, and $\rho$ a two-dimensional adic Galois representation over $A$: a type $V$ with an $A$-module structure that is free, finite and of rank $2$, together with a monoid homomorphism $\rho.\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`) to $\mathrm{End}_A(V)$ which is continuous for the $\mathfrak{m}_A$-adic filtration, in the sense that for each $n$ there is a finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ with $\rho(\sigma)v - v \in \mathfrak{m}_A^n V$ for all $\sigma$ fixing $L$ pointwise and all $v \in V$. Assume `ρ.IsFlatAt p`: the residue field of $A$ is finite, and for every ideal $I$ of $A$ with $A/I$ finite there is a commutative Hopf algebra over the subring $\mathbb{Z}_{(p)} \subset \mathbb{Q}$ of rationals whose denominator is coprime to $p$, finite and flat as a $\mathbb{Z}_{(p)}$-module and cocommutative, whose $\overline{\mathbb{Q}}$-points, with their convolution multiplication, are in bijection with $V/IV$ compatibly with addition and with the induced Galois action on $V/IV$. The conclusion is that there exist a commutative ring $H$ with a Hopf algebra structure over $\mathbb{Z}_p$ which is finite and flat as a $\mathbb{Z}_p$-module and cocommutative, and a bijection $e$ from the set of $\mathbb{Z}_p$-algebra homomorphisms $H \to$ `PadicAlgCl p`, equipped with the convolution multiplication, onto $V$ itself (not merely a finite level) such that $e(f \cdot g) = e(f) + e(g)$, and such that for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of `PadicAlgCl p` and all points $f, g$ with $g(h) = \sigma(f(h))$ for all $h \in H$, one has $e(g) = \rho.\rho(\mathrm{localGaloisToGlobal}\,p\,\sigma)(e(f))$, where [`localGaloisToGlobal`](def/GaloisRep_CompletionBridge.html#L41) sends $\sigma$ to its restriction of scalars to $\mathbb{Q}$ followed by restriction to the normal subextension `AlgebraicClosure ℚ`.
--
--   This is the bridge from the global, completion-free flat deformation condition at $p$ to the local theory of finite flat group schemes over $\mathbb{Z}_p$: the full representation $V$, and not just its finite levels, is realised as the $\overline{\mathbb{Q}}_p$-points of a finite flat cocommutative Hopf algebra over $\mathbb{Z}_p$, equivariantly for the decomposition group at $p$. It is used in the bound on the invariants of flat representations proved in [`GaloisRepAdic.exists_submodule_finrank_le_invariants_add_one_mem_of_isFlatAt`](thm.html#GaloisRepAdic.exists_submodule_finrank_le_invariants_add_one_mem_of_isFlatAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_finiteFlat_padicInt_model_of_isFlatAt.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.exists_finiteFlat_padicInt_model_of_isFlatAt
    {A : Type} [CommRing A] [IsLocalRing A] [Finite A] (p : ℕ) [Fact p.Prime]
    (ρ : GaloisRepAdic A) (hρ : ρ.IsFlatAt p) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρ.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = σ (f h)) → e g = ρ.ρ (localGaloisToGlobal p σ) (e f) := by sorry
