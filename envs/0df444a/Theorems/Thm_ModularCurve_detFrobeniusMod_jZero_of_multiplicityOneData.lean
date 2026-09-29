-- Prove2me | Theorems.Thm_ModularCurve_detFrobeniusMod_jZero_of_multiplicityOneData
-- name    : ModularCurve.detFrobeniusMod_jZero_of_multiplicityOneData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/989ea377-9984-5a69-b439-b02ef0f430b8
-- title:
--   Determinant of Frobenius on J₀(M)[𝔪] equals ℓ
-- statement:
--   Let $M$ be a nonzero natural number, $p$ a prime and $\mathfrak m$ an ideal of `HeckeAlg`, the polynomial ring $\mathbb Z[T_q : q \text{ prime}]$ on the set of primes. Give $\mathrm{JZero}\,M$, the group $\mathrm{Pic}^0$ of degree-zero divisor classes of the base-changed modular function field of level $M$ over $\overline{\mathbb Q}$, the `HeckeAlg`-module structure `heckeModuleBar M`. Assume `MultiplicityOneData p (JZero M) 𝔪`, that is: $\mathfrak m$ is maximal, the image of $p$ lies in $\mathfrak m$, and the $\mathfrak m$-torsion submodule $\{x : \mathfrak m \cdot x = 0\}$ has dimension exactly $2$ over the residue field $\mathrm{HeckeAlg}/\mathfrak m$; assume also that the natural action of $\overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ on $\mathrm{JZero}\,M$ commutes with the `HeckeAlg`-action. The conclusion is `DetFrobeniusMod` for $K = \mathbb Q$, $L = \overline{\mathbb Q}$, level $M$, residue characteristic $p$ and the module $\mathrm{JZero}\,M$: for every prime $\ell$ with $\ell \nmid Mp$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, and every $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ lying in the decomposition subgroup of $A$ and acting on the residue field of $A$ by $x \mapsto x^{\ell}$, the determinant of the $\mathrm{HeckeAlg}/\mathfrak m$-linear endomorphism of the $\mathfrak m$-torsion induced by $\sigma$ equals the image of $\ell$ in $\mathrm{HeckeAlg}/\mathfrak m$.
--
--   This is the determinant clause of the Eichler–Shimura package for the modular Jacobian: under multiplicity one the $\mathfrak m$-torsion of $J_0(M)$ is a two-dimensional Galois representation over $\mathrm{HeckeAlg}/\mathfrak m$ whose determinant is the cyclotomic character, read off at Frobenius elements via the Weil pairing on the Jacobian. It feeds [`ModularCurve.det_mTorsionGaloisRep_eq_natCast_of_multiplicityOneData`](thm.html#ModularCurve.det_mTorsionGaloisRep_eq_natCast_of_multiplicityOneData), which extracts the determinant value at a single Frobenius element.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_detFrobeniusMod_jZero_of_multiplicityOneData.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HeckeGalois_EichlerShimura

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.detFrobeniusMod_jZero_of_multiplicityOneData
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg)
    (hmultone :
      letI := heckeModuleBar M
      MultiplicityOneData p (JZero M) 𝔪)
    (hsmul :
      letI := heckeModuleBar M
      SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero M)) :
    letI := heckeModuleBar M
    haveI : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero M) := hsmul
    DetFrobeniusMod (K := ℚ) (L := AlgebraicClosure ℚ) M p (JZero M) 𝔪 := by sorry
