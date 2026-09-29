-- Prove2me | Theorems.Thm_ModularCurve_natCard_iInf_ker_mapCotangent_baseChange_model_jZero_torsion_eq_card_torsionBySet_intLattice_quotient
-- name    : ModularCurve.natCard_iInf_ker_mapCotangent_baseChange_model_jZero_torsion_eq_card_torsionBySet_intLattice_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/1d17d6c7-74f4-58cd-ae40-8dae754a7dfd
-- title:
--   Hecke torsion in the cotangent space of J₀(N)[p]
-- statement:
--   Fix $N\ge 1$, a prime $p$ with $p\neq 2$ and $p\nmid N$, and an ideal $\mathfrak m$ of the Hecke algebra `HeckeAlg` $=\mathbb Z[X_\ell:\ell\text{ prime}]$ (a polynomial ring on the primes). Let $A$ be a commutative ring that is a Hopf algebra over the subring $\mathbb Z_{(p)}=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb Q$ (rationals whose denominator is coprime to $p$), finite and flat as a $\mathbb Z_{(p)}$-module and cocommutative as a coalgebra. Equip $J_0(N)=$ `JZero N`, the degree-zero divisor class group of the function field `modularFunctionFieldBar N` over $\overline{\mathbb Q}$, with the Hecke action `heckeModuleBar N`, and the lattice [`CuspForm.intLattice N 2`](def/CuspForm_IntegralStructure.html#L3) of weight-two cusp forms on $\Gamma_0(N)$ spanned by those with integral $q$-coefficients with the Hecke action of [`CuspForm.latticeHeckeFamily N`](def/CuspForm_LatticeHeckeFamily.html#L13) (each prime $\ell$ acting by $U_\ell$ if $\ell\mid N$ and by $T_\ell$ otherwise). The assertion is: for every bijection $e$ from `WithConv` of the set of $\mathbb Z_{(p)}$-algebra maps $A\to\overline{\mathbb Q}$ onto the $p$-torsion `Submodule.torsionBy ℤ (JZero N) ((p:ℤ)^1)` which turns the multiplication of `WithConv` into addition and satisfies $e(\sigma\circ f)=\sigma\cdot e(f)$ for $\sigma\in\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$; for every family $\varphi$ of $\mathbb Z_{(p)}$-algebra endomorphisms of $A$ indexed by `HeckeAlg` with $e(f\circ\varphi_t)=t\cdot e(f)$; for every family $\psi$ of bialgebra endomorphisms of $\mathbb F_p\otimes_{\mathbb Z_{(p)}}A$ whose underlying algebra maps are $\mathrm{id}\otimes\varphi_t$; and given that each $\psi_t$ carries the augmentation ideal $I=\ker(\varepsilon)$ into itself, the intersection over $t\in\mathfrak m$ of the kernels of the endomorphisms of the cotangent space $I/I^2$ induced by $\psi_t$ has the same number of elements as the $\mathfrak m$-torsion submodule of $(\,$[`CuspForm.intLattice N 2`](def/CuspForm_IntegralStructure.html#L3)$)/p$.
--
--   This is the counting form of the $q$-expansion principle for $J_0(N)$: the cotangent space at the origin of the special fibre of a finite flat Hecke-equivariant model of $J_0(N)[p]$ is measured, ideal by ideal in the Hecke algebra, against weight-two cusp forms modulo $p$. It feeds the Dieudonné-module count [`ModularCurve.natCard_dieudonneModule_quot_range_verschiebung_sup_range_map_hecke_eq_card_torsionBySet_intLattice_quotient`](thm.html#ModularCurve.natCard_dieudonneModule_quot_range_verschiebung_sup_range_map_hecke_eq_card_torsionBySet_intLattice_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_iInf_ker_mapCotangent_baseChange_model_jZero_torsion_eq_card_torsionBySet_intLattice_quotient.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_CuspForm_LatticeHeckeFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
open scoped TensorProduct

theorem ModularCurve.natCard_iInf_ker_mapCotangent_baseChange_model_jZero_torsion_eq_card_torsionBySet_intLattice_quotient
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) (𝔪 : Ideal HeckeAlg)
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
      ∀ hI : ∀ t : HeckeAlg,
          RingHom.ker (Bialgebra.counitAlgHom (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A)) ≤
            (RingHom.ker (Bialgebra.counitAlgHom (ZMod p)
              ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A))).comap
              (ψ t : (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A →ₐ[ZMod p]
                (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A),
      Nat.card ↥(⨅ (t : HeckeAlg) (_ : t ∈ 𝔪), LinearMap.ker
          (Ideal.mapCotangent
            (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A)))
            (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A)))
            (ψ t : (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A →ₐ[ZMod p]
              (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) (hI t)))
        = Nat.card ↥(Submodule.torsionBySet HeckeAlg
            (↥(CuspForm.intLattice N 2) ⧸ (Ideal.span {((p : ℕ) : HeckeAlg)} •
              (⊤ : Submodule HeckeAlg ↥(CuspForm.intLattice N 2)))) 𝔪) := by sorry
