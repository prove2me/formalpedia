-- Prove2me | Theorems.Thm_ModularCurve_frobenius_comp_verschiebung_eq_unit_counit_of_model_jZero_torsion
-- name    : ModularCurve.frobenius_comp_verschiebung_eq_unit_counit_of_model_jZero_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/09b0d475-e59a-5e59-9882-746c56938cdf
-- title:
--   Frobenius after Verschiebung is trivial on the Cartier dual
-- statement:
--   Fix a nonzero natural number $M$ and a prime $p$, and let $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) be the subring of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$. Let $H$ be a commutative ring carrying a Hopf algebra structure over $R$ that is finite and free as an $R$-module and whose comultiplication is cocommutative. Assume given a bijection $e$ from the set of $R$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$, regarded with its convolution multiplication via `WithConv`, onto the subgroup of $J_0(M) = \mathrm{Pic}^0$ of the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $M$ cut out by the intersection of the $p$-torsion submodule with the union over $m$ of the kernels of $\overline{T_p}^{\,m}$, where $\overline{T_p} =$ `heckeOperatorBar M p` is the Hecke endomorphism at $p$; and assume $e$ carries the convolution product to addition, $e(fg) = e(f) + e(g)$. Write $H_k = \mathbb{Z}/p \otimes_R H$ for the reduction. Then for every bialgebra endomorphism $F_k$ of $H_k$ with $F_k(x) = x^p$ for all $x$, and every $\mathbb{Z}/p$-algebra endomorphism $F_D$ of the Cartier dual $D =$ [`CartierDual (ZMod p) H_k`](def/HopfAlgebra_CartierDual.html#L12) with $F_D(\psi) = \psi^p$ for all $\psi$, the $\mathbb{Z}/p$-linear composite of [`CartierDual.map`](def/HopfAlgebra_CartierDualMap.html#L102) $F_k$ followed by $F_D$ equals the counit of $D$ followed by the structure map $\mathbb{Z}/p \to D$. Existence of such $F_k$, $F_D$ is not asserted; the conclusion is for an arbitrary such pair.
--
--   This is the relation $F \circ V = p = 0$ on the special fibre of a finite flat model of the $T_p$-nilpotent part of $J_0(M)[p]$: Frobenius composed with Verschiebung on the Cartier dual is multiplication by $p$, and the model is killed by $p$ because its $\overline{\mathbb{Q}}$-points are. It feeds the construction of such a model together with its Frobenius–Verschiebung data in [`ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeNilpotent_frobenius_verschiebung_reductionModL`](thm.html#ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeNilpotent_frobenius_verschiebung_reductionModL).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frobenius_comp_verschiebung_eq_unit_counit_of_model_jZero_torsion.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_HopfAlgebra_CartierDualMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.frobenius_comp_verschiebung_eq_unit_counit_of_model_jZero_torsion
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero M) (p : ℤ) ⊓
            ⨆ m : ℕ, LinearMap.ker (heckeOperatorBar M ⟨p, hp.out⟩ ^ m)))
    (he_add : ∀ f g, e (f * g) = e f + e g) :
    ∀ (Fk : TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H →ₐc[ZMod p]
        TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H),
      (∀ x, Fk x = x ^ p) →
    ∀ (FD : CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H) →ₐ[ZMod p]
        CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)),
      (∀ ψ, FD ψ = ψ ^ p) →
      (FD : CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H) →ₗ[ZMod p]
          CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)) ∘ₗ
          (CartierDual.map Fk :
            CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H) →ₗ[ZMod p]
              CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)) =
        Algebra.linearMap (ZMod p)
            (CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)) ∘ₗ
          Coalgebra.counit := by sorry
