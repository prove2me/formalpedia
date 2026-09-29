-- Prove2me | Theorems.Thm_GaloisRepAdic_isFlatAt_of_surjective_tateModule_of_forall_exists_finiteFlat_pi_torsion
-- name    : GaloisRepAdic.isFlatAt_of_surjective_tateModule_of_forall_exists_finiteFlat_pi_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/8b7c3b0b-f8bf-526d-a9a5-f95ed06dedf7
-- title:
--   Flatness at p via an equivariant quotient of a Tate module
-- statement:
--   Fix a prime $p$ and an abelian group $J$ carrying a distributive action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (realised as $\overline{\mathbb Q}$-algebra automorphisms of $\overline{\mathbb Q}$ over $\mathbb Q$), such that the Tate module $\mathrm{TateModule}\ p\ J$ — the group of sequences $(x_n)$ in $J$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$ — is a finite $\mathbb Z_p$-module. Assume the hypothesis `hJ`: for all $n, b \in \mathbb N$ there is a commutative ring $G$ with a Hopf algebra structure over the subring $\mathrm{ratLocalizedAt}\ p \subseteq \mathbb Q$ of rationals whose denominator is coprime to $p$, finite and flat as a module over that subring and cocommutative as a coalgebra, together with a bijection $e$ from the convolution monoid `WithConv` of $\mathrm{ratLocalizedAt}\ p$-algebra maps $G \to \overline{\mathbb Q}$ onto $\mathrm{Fin}\ b \to J[p^n]$ (the $p^n$-torsion submodule of $J$ over $\mathbb Z$), which sends products to sums and is Galois-equivariant in the sense that whenever $g = \sigma \circ f$ pointwise on $G$, each component satisfies $e\,g\,i = \sigma \cdot e\,f\,i$ in $J$. Let $O$ be a characteristic-zero discrete valuation domain with finite residue field, a $\mathbb Z_p$-algebra with $p$ in its maximal ideal, and let $K$ be a fraction field of $O$, a $\mathbb Z_p$-algebra compatibly with the tower $\mathbb Z_p \to O \to K$. Let $\rho$ be an adic Galois representation over $O$: a free finite $O$-module $\rho.V$ of rank $2$ with a monoid homomorphism $\rho.\rho$ from the Galois group to $\mathrm{End}_O(\rho.V)$ which is $\mathfrak m_O$-adically continuous (for each $n$ some finite subextension $L/\mathbb Q$ of $\overline{\mathbb Q}$ exists such that elements fixing $L$ pointwise act trivially modulo $\mathfrak m_O^n \rho.V$). Suppose finally that there is a surjective $K$-linear map $\pi : K \otimes_{\mathbb Z_p} \mathrm{TateModule}\ p\ J \to K \otimes_O \rho.V$ intertwining, for every $\sigma$, the base change to $K$ of the componentwise action of $\sigma$ on the Tate module with the base change of $\rho.\rho\,\sigma$. The conclusion is $\rho.\mathrm{IsFlatAt}\ p$: the residue field of $O$ is finite, and for every ideal $I \subseteq O$ with $O/I$ finite there are a finite flat cocommutative Hopf algebra $H$ over $\mathrm{ratLocalizedAt}\ p$ and a bijection from the convolution monoid of its $\overline{\mathbb Q}$-points onto $\rho.V/(I \cdot \rho.V)$ carrying products to sums and carrying post-composition with $\sigma$ to the induced action $\rho.\mathrm{levelAction}\ I\ \sigma$.
--
--   This is the transfer of finite flatness at $p$ from a Galois module $J$ whose $p$-power torsion is prolongable to a finite flat commutative group scheme over $\mathbb Z_{(p)}$ to any two-dimensional $O$-adic representation obtained as an equivariant quotient of the rational Tate module of $J$, the flatness half of the local conditions at $p$ in the Frey-curve argument. It is used by [`GaloisRepAdic.isFlatAt_of_isPrimitiveForm_of_not_dvd`](thm.html#GaloisRepAdic.isFlatAt_of_isPrimitiveForm_of_not_dvd), and the proof invokes the finite-flat descent lemmas [`GaloisRep.exists_finiteFlat_sub_of_equivariant_injection`](thm.html#GaloisRep.exists_finiteFlat_sub_of_equivariant_injection) and [`GaloisRep.exists_finiteFlat_quotient_of_equivariant_surjection`](thm.html#GaloisRep.exists_finiteFlat_quotient_of_equivariant_surjection) together with finiteness of $O$ over $\mathbb Z_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isFlatAt_of_surjective_tateModule_of_forall_exists_finiteFlat_pi_torsion.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem GaloisRepAdic.isFlatAt_of_surjective_tateModule_of_forall_exists_finiteFlat_pi_torsion
    (p : ℕ) [Fact p.Prime]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [Module.Finite ℤ_[p] (TateModule p J)]

    (hJ : ∀ n b : ℕ,
      ∃ (G : Type) (_ : CommRing G) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) G),
        Module.Finite (GaloisRep.ratLocalizedAt p) G ∧ Module.Flat (GaloisRep.ratLocalizedAt p) G ∧
        Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) G ∧
        ∃ e : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
            (Fin b → ↥(Submodule.torsionBy ℤ J ((p ^ n : ℕ) : ℤ)).toAddSubgroup),
          (∀ f g, e (f * g) = e f + e g) ∧
          ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
            (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ x : G, g x = σ (f x)) →
              ∀ i : Fin b,
                ((e g i : ↥(Submodule.torsionBy ℤ J ((p ^ n : ℕ) : ℤ)).toAddSubgroup) : J) =
                  σ • ((e f i : ↥(Submodule.torsionBy ℤ J ((p ^ n : ℕ) : ℤ)).toAddSubgroup) : J))

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [CharZero O] [Algebra ℤ_[p] O]
    (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] [Algebra ℤ_[p] K]
    [IsScalarTower ℤ_[p] O K]

    (ρ : GaloisRepAdic O)
    (π : K ⊗[ℤ_[p]] TateModule p J →ₗ[K] K ⊗[O] ρ.V) (hπ : Function.Surjective π)
    (hπeq : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : K ⊗[ℤ_[p]] TateModule p J),
      π ((TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange K x) =
        (ρ.ρ σ).baseChange K (π x)) :
    ρ.IsFlatAt p := by sorry
