-- Prove2me | Theorems.Thm_ModularCurve_natCard_dieudonneModule_quot_range_verschiebung_sup_range_map_hecke_eq_card_torsionBySet_intLattice_quotient
-- name    : ModularCurve.natCard_dieudonneModule_quot_range_verschiebung_sup_range_map_hecke_eq_card_torsionBySet_intLattice_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/ce700640-7412-5cea-873c-29ace3ccdb5b
-- title:
--   Verschiebung cokernel of the Dieudonné module of J₀(N)[p] at 𝔪
-- statement:
--   Fix $N\ge 1$, a prime $p\ne 2$ with $p\nmid N$, and an ideal $\mathfrak m$ of $\mathbb{T}=\mathrm{MvPolynomial}\ \mathrm{Nat.Primes}\ \mathbb{Z}$, the polynomial ring over $\mathbb{Z}$ on indeterminates indexed by the primes. Let $A$ be a commutative ring which is a cocommutative Hopf algebra over the subring $\mathbb{Z}_{(p)}\subset\mathbb{Q}$ of rationals whose denominator is coprime to $p$, finite and flat as a module over it. Here $\mathbb{T}$ acts on $JZero\ N=\mathrm{Pic}^0$ of the modular function field of level $N$ over $\overline{\mathbb{Q}}$ by `heckeModuleBar`, and on the lattice $\mathrm{intLattice}\ N\ 2$, the $\mathbb{Z}$-span of the weight-two cusp forms on $\Gamma_0(N)$ all of whose $q$-expansion coefficients are integers, through the commuting family sending the indeterminate at $\ell$ to the Hecke operator at $\ell$. Then, for every bijection $e$ from `WithConv` of the set of $\mathbb{Z}_{(p)}$-algebra maps $A\to\overline{\mathbb{Q}}$ onto the $p$-torsion submodule $\{x\in JZero\ N: p^1x=0\}$ satisfying: $e(fg)=e(f)+e(g)$; for $\sigma\in\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and points $f,g$ with $g(h)=\sigma(f(h))$ for all $h\in A$, $e(g)=\sigma\cdot e(f)$; and, for a family $\varphi$ of $\mathbb{Z}_{(p)}$-algebra endomorphisms of $A$ indexed by $\mathbb{T}$, for $t\in\mathbb{T}$ and points $f,g$ with $g(h)=f(\varphi_t h)$ for all $h$, $e(g)=t\cdot e(f)$; and for every family $\psi$ of $\mathbb{F}_p$-bialgebra endomorphisms of $\mathbb{F}_p\otimes_{\mathbb{Z}_{(p)}}A$ indexed by $\mathbb{T}$ whose underlying algebra maps are $\mathrm{id}\otimes\varphi_t$, the number of elements of the quotient of the Dieudonné module $\mathrm{DieudonneModule}\ \mathbb{F}_p\ p\ (\mathbb{F}_p\otimes A)$ (the direct limit of the truncated Witt-vector homomorphism groups) by the sum of the range of Verschiebung and the supremum of the ranges of the maps induced by $\psi_t$ for $t\in\mathfrak m$ equals the number of elements of the $\mathfrak m$-torsion of $(\mathrm{intLattice}\ N\ 2)/p\,(\mathrm{intLattice}\ N\ 2)$.
--
--   This is the Oda–Mazur count of the Dieudonné module of the $p$-torsion of the Jacobian of $X_0(N)$ in characteristic $p$, in the form used by Mazur: the cokernel of Verschiebung together with the Hecke ideal $\mathfrak m$ is measured by the $\mathfrak m$-torsion in the mod $p$ reduction of the integral lattice of weight-two cusp forms. It combines a general cardinality formula for Dieudonné modules killed by $p$, the comparison of the Cartier dual of the base change of the Hecke model of $J_0(N)[p]$ with cotangent data, and is used for the bound [`ModularCurve.pow_finrank_primitives_baseChange_le_card_torsionBySet_intLattice_quotient`](thm.html#ModularCurve.pow_finrank_primitives_baseChange_le_card_torsionBySet_intLattice_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_dieudonneModule_quot_range_verschiebung_sup_range_map_hecke_eq_card_torsionBySet_intLattice_quotient.lean

import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_CuspForm_LatticeHeckeFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
open scoped TensorProduct

theorem ModularCurve.natCard_dieudonneModule_quot_range_verschiebung_sup_range_map_hecke_eq_card_torsionBySet_intLattice_quotient
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N)
    (𝔪 : Ideal HeckeAlg)
    (A : Type) [CommRing A] [HopfAlgebra (GaloisRep.ratLocalizedAt p) A]
    [Module.Finite (GaloisRep.ratLocalizedAt p) A] [Module.Flat (GaloisRep.ratLocalizedAt p) A]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) A] :
    letI := heckeModuleBar N
    letI := (CuspForm.latticeHeckeFamily N).module
    ∀ e : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
        ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)),
      (∀ f g : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          e (f * g) = e f + e g) →
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : A, g h = σ (f h)) → ((e g : JZero N)) = σ • (e f : JZero N)) →
      ∀ φ : HeckeAlg → (A →ₐ[GaloisRep.ratLocalizedAt p] A),
        (∀ (t : HeckeAlg) (f g : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ h : A, g h = f (φ t h)) → ((e g : JZero N)) = t • (e f : JZero N)) →
      ∀ ψ : HeckeAlg →
          ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A →ₐc[ZMod p] (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A),
        (∀ t : HeckeAlg,
            (ψ t : (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A →ₐ[ZMod p]
                (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) =
              Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (φ t)) →
      Nat.card (Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) ⧸
          ((Deformation.DieudonneModule.verschiebung (ZMod p) p
                ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A)).range ⊔
            ⨆ (t : HeckeAlg) (_ : t ∈ 𝔪),
              (Deformation.DieudonneModule.map (ZMod p) p (ψ t)).range))
        = Nat.card ↥(Submodule.torsionBySet HeckeAlg
            (↥(CuspForm.intLattice N 2) ⧸ (Ideal.span {((p : ℕ) : HeckeAlg)} •
              (⊤ : Submodule HeckeAlg ↥(CuspForm.intLattice N 2)))) 𝔪) := by sorry
