-- Prove2me | Theorems.Thm_ModularCurve_det_mTorsionGaloisRep_eq_natCast_of_multiplicityOneData
-- name    : ModularCurve.det_mTorsionGaloisRep_eq_natCast_of_multiplicityOneData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/8bf7a14a-a87b-59b5-a0fe-119304486494
-- title:
--   Cyclotomic determinant of the 𝔪-torsion representation of J₀(M)
-- statement:
--   Let $M$ be a nonzero natural number, $p$ a prime, and $\mathfrak m$ an ideal of the abstract Hecke algebra `HeckeAlg`, the polynomial ring $\mathbb Z[T_\ell : \ell \text{ prime}]$. The group $J :=$ `JZero M` of degree-zero divisor classes of the modular function field of level $M$ base-changed to $\overline{\mathbb Q}$ carries the `HeckeAlg`-module structure `heckeModuleBar M` (the action through the Hecke operators when these commute, and the action through evaluation of all variables at $0$ otherwise), and a `DistribMulAction` of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) = \overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$. Assume `MultiplicityOneData p J 𝔪`, that is: $\mathfrak m$ is maximal, $p \in \mathfrak m$, and the $\mathfrak m$-torsion `heckeTorsion J 𝔪` (the elements killed by every element of $\mathfrak m$) has dimension $2$ over the residue field `HeckeAlg ⧸ 𝔪`; assume also that the Galois action on $J$ commutes with the Hecke action, so that $\sigma \mapsto (x \mapsto \sigma \cdot x)$ is a homomorphism `mTorsionGaloisRep` from the Galois group to the `HeckeAlg ⧸ 𝔪`-linear endomorphisms of the $\mathfrak m$-torsion. Then for every Galois element $\sigma$ and every natural number $a$ such that $\sigma\zeta = \zeta^a$ for all $\zeta \in \overline{\mathbb Q}$ with $\zeta^p = 1$, the determinant of $\sigma$ acting on the $\mathfrak m$-torsion equals the image of $a$ in `HeckeAlg ⧸ 𝔪`.
--
--   This identifies the determinant of the two-dimensional residual representation attached to a maximal ideal $\mathfrak m$ of residue characteristic $p$ with the mod-$p$ cyclotomic character, in the form used when comparing the Galois action on $J_0(M)[\mathfrak m]$ with local data. It is cited in the analysis of the toric part of the $\mathfrak m$-torsion at $p$, namely in the bound [`ModularCurve.JZeroNeronObjectAtP.natCard_toricPts_inf_heckeTorsion_le`](thm.html#ModularCurve.JZeroNeronObjectAtP.natCard_toricPts_inf_heckeTorsion_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_det_mTorsionGaloisRep_eq_natCast_of_multiplicityOneData.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HeckeGalois_EichlerShimura

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.det_mTorsionGaloisRep_eq_natCast_of_multiplicityOneData
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg)
    (hmultone :
      letI := heckeModuleBar M
      MultiplicityOneData p (JZero M) 𝔪)
    (hsmul :
      letI := heckeModuleBar M
      SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero M)) :
    letI := heckeModuleBar M
    haveI : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero M) := hsmul
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ a) →
        LinearMap.det (mTorsionGaloisRep (JZero M) 𝔪 σ) = (a : HeckeAlg ⧸ 𝔪) := by sorry
