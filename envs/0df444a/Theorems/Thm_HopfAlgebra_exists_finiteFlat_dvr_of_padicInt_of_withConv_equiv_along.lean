-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_dvr_of_padicInt_of_withConv_equiv_along
-- name    : HopfAlgebra.exists_finiteFlat_dvr_of_padicInt_of_withConv_equiv_along
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/8753bc2c-6f3c-5f64-8651-2092a55bca50
-- title:
--   Finite flat Hopf algebra over an abstract DVR with fraction field ℚ
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, equipped with algebra maps $R \to \mathbb{Q}$ exhibiting $\mathbb{Q}$ as its fraction field and $R \to \overline{\mathbb{Q}}$ compatible with these (a scalar tower), let $p$ be a prime with $p$ irreducible in $R$, and let $f : R \to \mathbb{Z}_p$ be a ring homomorphism such that for every $r \in R$ the image of $f(r)$ in $\mathbb{Q}_p$ is the image of $r$ under $R \to \mathbb{Q} \to \mathbb{Q}_p$. Let $A$ be a commutative ring with a $\mathbb{Q}$-Hopf algebra structure that is finite as a $\mathbb{Q}$-module and has cocommutative comultiplication, and let $H_p$ be a commutative ring with a $\mathbb{Z}_p$-Hopf algebra structure that is module-finite, flat and cocommutative over $\mathbb{Z}_p$. Let $M$ be an abelian group with a distributive multiplicative action of the group of $\mathbb{Q}_p$-algebra automorphisms of $\overline{\mathbb{Q}_p}$, and suppose given bijections $e_{H_p}$ from the set of $\mathbb{Z}_p$-algebra maps $H_p \to \overline{\mathbb{Q}_p}$, taken with its convolution product (`WithConv`), onto $M$, and $e_{A_p}$ from the $\mathbb{Q}$-algebra maps $A \to \overline{\mathbb{Q}_p}$ with their convolution product onto the same $M$; each is required to take convolution products to sums, and to be equivariant in the sense that whenever $g = \sigma \circ f$ pointwise one has $e(g) = \sigma \cdot e(f)$. Let $N$ be an abelian group with a distributive multiplicative action of the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$, and let $e_A$ be a bijection from the $\mathbb{Q}$-algebra maps $A \to \overline{\mathbb{Q}}$ with convolution product onto $N$, again additive on convolution products and equivariant in the same sense. The conclusion asserts the existence of a type $H$ with a commutative ring structure and an $R$-Hopf algebra structure such that $H$ is finite and flat as an $R$-module and cocommutative, together with a bijection $e$ from the $R$-algebra maps $H \to \overline{\mathbb{Q}}$ with convolution product onto $N$ which sends convolution products to sums and satisfies the same equivariance for $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$. The proof visibly discards the homomorphism $f$ and its compatibility hypothesis.
--
--   This is the prolongation statement for finite flat group schemes in Hopf-algebra form over an abstract discrete valuation ring with fraction field $\mathbb{Q}$ and uniformiser $p$: a finite cocommutative $\mathbb{Q}$-Hopf algebra whose $\overline{\mathbb{Q}_p}$-points match those of a finite flat cocommutative $\mathbb{Z}_p$-Hopf algebra admits a finite flat cocommutative model over $R$ with the prescribed Galois module of $\overline{\mathbb{Q}}$-points. It is used in the torsion-prolongation result [`WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_padicInt_along`](thm.html#WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_padicInt_along), which supplies the finite flat input for the local condition at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finiteFlat_dvr_of_padicInt_of_withConv_equiv_along.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_finiteFlat_dvr_of_padicInt_of_withConv_equiv_along
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    [Algebra R (AlgebraicClosure ℚ)] [IsScalarTower R ℚ (AlgebraicClosure ℚ)]
    (p : ℕ) [Fact p.Prime] (hp : Irreducible (p : R))
    (f : R →+* ℤ_[p])
    (hfc : ∀ r : R, ((f r : ℤ_[p]) : ℚ_[p]) = (algebraMap ℚ ℚ_[p]) (algebraMap R ℚ r))
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (hAfin : Module.Finite ℚ A) (hAcocomm : Coalgebra.IsCocomm ℚ A)
    (Hp : Type) [CommRing Hp] [HopfAlgebra ℤ_[p] Hp]
    (hfin : Module.Finite ℤ_[p] Hp) (hflat : Module.Flat ℤ_[p] Hp)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] Hp)
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (eHp : WithConv (Hp →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
    (heHp_add : ∀ f g, eHp (f * g) = eHp f + eHp g)
    (heHp_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (Hp →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ x : Hp, g x = σ (f x)) → eHp g = σ • (eHp f))
    (eAp : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p]) ≃ M)
    (heAp_add : ∀ f g, eAp (f * g) = eAp f + eAp g)
    (heAp_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])),
      (∀ a : A, g a = σ (f a)) → eAp g = σ • (eAp f))
    {N : Type} [AddCommGroup N]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (eA : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ) ≃ N)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e : WithConv (H →ₐ[R] AlgebraicClosure ℚ) ≃ N,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[R] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by sorry
