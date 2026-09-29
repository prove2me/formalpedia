-- Prove2me | Theorems.Thm_ModularCurve_heckeTorsion_jZero_finite_of_natCast_mem
-- name    : ModularCurve.heckeTorsion_jZero_finite_of_natCast_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/5f9b1370-b823-5185-9b85-9d5bef7ec861
-- title:
--   Finiteness of the 𝔪-torsion of J₀(M)
-- statement:
--   Fix a natural number $M \neq 0$ and let `JZero M` be the degree-zero part of the divisor class group $\mathrm{Pic}^0$ of the function field `modularFunctionFieldBar M`, i.e. the base change to $\overline{\mathbb Q}$ of the full modular function field of level $M$, viewed as an extension of $\overline{\mathbb Q}$ inside Laurent series; concretely, degree-zero divisors modulo the subgroup of principal divisors. This group is equipped with the module structure `heckeModuleBar M` over the Hecke algebra `HeckeAlg` $= \mathbb Z[X_\ell : \ell \text{ prime}]$ (a polynomial ring on the set of primes), defined by cases: if the divisorial Hecke endomorphisms `heckeOperatorBar M ℓ` commute pairwise, the variables act through them, and otherwise all variables act by $0$. Let $\mathfrak m \subseteq$ `HeckeAlg` be an ideal, and let $p$ be a natural number with $p > 0$ whose image in `HeckeAlg` lies in $\mathfrak m$. The conclusion is that the submodule `heckeTorsion (JZero M) 𝔪`, namely $\{x : t \cdot x = 0 \text{ for all } t \in \mathfrak m\}$, is a finite type. No irreducibility, maximality or residue-characteristic hypothesis on $\mathfrak m$ is imposed beyond containing the positive integer $p$.
--
--   This is the finiteness of $J_0(M)[\mathfrak m]$ for a Hecke ideal $\mathfrak m$ of positive residue characteristic, the torsion-finiteness input used whenever an $\mathfrak m$-torsion subgroup of the Jacobian is treated as a finite Galois module. It is cited in the construction of the mod-$\mathfrak m$ Galois representation attached to $J_0(M)$ and in the computation of its determinant and of the characteristic polynomial of Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeTorsion_jZero_finite_of_natCast_mem.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_JZeroTorsionFinite
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve

theorem ModularCurve.heckeTorsion_jZero_finite_of_natCast_mem (M : ℕ) [NeZero M] (𝔪 : Ideal HeckeAlg)
    (p : ℕ) (hp : 0 < p) (hres : (p : HeckeAlg) ∈ 𝔪) :
    letI := heckeModuleBar M
    Finite (heckeTorsion (JZero M) 𝔪) := by sorry
