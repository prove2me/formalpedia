-- Prove2me | Theorems.Thm_GaloisRep_exists_ideal_le_comap_includeRight_eq_of_natCast_mem
-- name    : GaloisRep.exists_ideal_le_comap_includeRight_eq_of_natCast_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/3f3e267c-bf53-54d8-965b-a1af67b4c221
-- title:
--   Going down along O → κ ⊗_ℤ₍ₚ₎ O at primes containing p
-- statement:
--   Let $p$ be a prime and write $R = \mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator (in lowest terms) is coprime to $p$. Let $\kappa$ be a field of characteristic $p$ equipped with an $R$-algebra structure, and let $O$ be a commutative $R$-algebra. Let $P \subseteq \mathfrak{q}$ be prime ideals of $O$ with $P \le \mathfrak{q}$, and assume the image of the natural number $p$ in $O$ lies in $P$. Let $\mathfrak{P}$ be a prime ideal of $\kappa \otimes_R O$ whose contraction along the $R$-algebra map $\mathrm{includeRight} : O \to \kappa \otimes_R O$, $b \mapsto 1 \otimes b$, is exactly $\mathfrak{q}$. The assertion is that there exists a prime ideal $\mathfrak{P}'$ of $\kappa \otimes_R O$ with $\mathfrak{P}' \le \mathfrak{P}$ whose contraction along the same map $\mathrm{includeRight}$ equals $P$. Thus primes of the base $O$ lying below $\mathfrak{q}$ and containing $p$ are hit by primes of $\kappa \otimes_R O$ lying below $\mathfrak{P}$.
--
--   This is the going-down property for the map $O \to \kappa \otimes_{\mathbb{Z}_{(p)}} O$, restricted to primes of $O$ containing $p$; the restriction is harmless because every prime of $\kappa \otimes_{\mathbb{Z}_{(p)}} O$ contracts to a prime containing $p$. It is used in the analysis of the mod $p$ fibre of the model of the modular curve, where a point of $\operatorname{Spec}(\kappa \otimes \mathcal{O})$ over a point of a branch $V(P)$ must be generised, in [`ModularCurve.XHDRModelAtP.exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le`](thm.html#ModularCurve.XHDRModelAtP.exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_ideal_le_comap_includeRight_eq_of_natCast_mem.lean

import Mathlib
import Definitions.Def_GaloisRep_RatLocalizedAtResidue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem GaloisRep.exists_ideal_le_comap_includeRight_eq_of_natCast_mem
    (p : ℕ) [Fact p.Prime]
    (κ : Type) [Field κ] [CharP κ p] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]
    (O : Type) [CommRing O] [Algebra ↥(GaloisRep.ratLocalizedAt p) O]
    (P 𝔮 : Ideal O) [P.IsPrime] [𝔮.IsPrime] (hP𝔮 : P ≤ 𝔮) (hpP : ((p : ℕ) : O) ∈ P)
    (𝔓 : Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] O)) [𝔓.IsPrime]
    (h𝔓 : 𝔓.comap (Algebra.TensorProduct.includeRight :
        O →ₐ[↥(GaloisRep.ratLocalizedAt p)] κ ⊗[↥(GaloisRep.ratLocalizedAt p)] O).toRingHom = 𝔮) :
    ∃ 𝔓' : Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] O), 𝔓' ≤ 𝔓 ∧ 𝔓'.IsPrime ∧
      𝔓'.comap (Algebra.TensorProduct.includeRight :
        O →ₐ[↥(GaloisRep.ratLocalizedAt p)] κ ⊗[↥(GaloisRep.ratLocalizedAt p)] O).toRingHom = P := by sorry
