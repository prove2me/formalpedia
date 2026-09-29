-- Prove2me | Theorems.Thm_ModularCurve_natCard_dieudonneModule_quot_range_verschiebung_le_of_local_local_model_heckeTorsion_jZero
-- name    : ModularCurve.natCard_dieudonneModule_quot_range_verschiebung_le_of_local_local_model_heckeTorsion_jZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/1618415f-8d93-5459-8048-fc92b1fa1700
-- title:
--   Verschiebung cokernel bound for a local–local model of J₀(N)[𝔪]
-- statement:
--   Fix $N\ge 1$ and a prime $p$ with $p\ne 2$ and $p\nmid N$, and let $\mathfrak m$ be a maximal ideal of the Hecke algebra `HeckeAlg` $=\mathbb Z[X_\ell : \ell \text{ prime}]$ (the polynomial ring on the primes) whose residue ring `HeckeAlg ⧸ 𝔪` is finite and which contains the image of $p$. Let $H$ be a commutative ring that is a cocommutative Hopf algebra, finite and free as a module, over the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb Q$ consisting of rationals whose denominator is coprime to $p$; assume $H$ is local and that its Cartier dual, the dual module [`CartierDual`](def/HopfAlgebra_CartierDual.html#L12), is local as a ring. Assume further given a bijection $e$ from `WithConv` of the set of algebra maps $H \to \overline{\mathbb Q}$ onto the $\mathfrak m$-torsion submodule $\{x : \mathfrak m \cdot x = 0\}$ of `JZero N`, the degree-zero divisor class group of the modular function field of level $N$ over $\overline{\mathbb Q}$ with its Hecke action `heckeModuleBar`, such that $e$ turns multiplication into addition and is equivariant for $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ in the sense that post-composing a point $f$ with $\sigma$ sends $e(f)$ to $\sigma \cdot e(f)$ in `JZero N`. Then the cardinality of the quotient of the Dieudonné module (the direct limit of the groups of Hopf-algebra-theoretic additive elements in truncated Witt vectors) of $\mathbb F_p \otimes H$ by the image of Verschiebung is at most the cardinality of `HeckeAlg ⧸ 𝔪`.
--
--   This is the step of Mazur's analysis of the Eisenstein ideal asserting that, for a local–local finite flat model of $J_0(N)[\mathfrak m]$, the cokernel of Verschiebung on the Dieudonné module of the special fibre has at most $\#(\mathbb T/\mathfrak m)$ elements, i.e. is at most one-dimensional over $\mathbb T/\mathfrak m$. It feeds the bound of $2$ for the dimension of $J_0(N)[\mathfrak m]$ over the residue field under absolute irreducibility.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_dieudonneModule_quot_range_verschiebung_le_of_local_local_model_heckeTorsion_jZero.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in
open scoped TensorProduct in

theorem ModularCurve.natCard_dieudonneModule_quot_range_verschiebung_le_of_local_local_model_heckeTorsion_jZero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hfin : Finite (HeckeAlg ⧸ 𝔪)) (hpm : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hloc : IsLocalRing H) (hdual : IsLocalRing (CartierDual (GaloisRep.ratLocalizedAt p) H))
    (e : letI := heckeModuleBar N
      WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥(heckeTorsion (JZero N) 𝔪))
    (he_add : letI := heckeModuleBar N
      ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), e (f * g) = e f + e g)
    (he_gal : letI := heckeModuleBar N
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = σ (f h)) →
          ((e g : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N) = σ • ((e f : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N)) :
    Nat.card (Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H) ⧸
        (Deformation.DieudonneModule.verschiebung (ZMod p) p
          ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H)).range) ≤
      Nat.card (HeckeAlg ⧸ 𝔪) := by sorry
