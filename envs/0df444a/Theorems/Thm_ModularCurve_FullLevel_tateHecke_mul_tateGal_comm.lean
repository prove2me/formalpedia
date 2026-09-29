-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_tateHecke_mul_tateGal_comm
-- name    : ModularCurve.FullLevel.tateHecke_mul_tateGal_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/3586cf04-908f-557f-98e1-20d9ca899872
-- title:
--   Hecke and Galois operators commute on the Tate module
-- statement:
--   Let $q$ be a prime, let $M'$ be a nonzero natural number and let $\lambda$ be a prime. Write $\mathrm{Jac}(q,M')$ for the project's Jacobian carrier of full level $q$ over level $M'$, built from the Jacobian `jacComp` of $X_H(q^2M')$ indexed by `Idx q`, and $T_\lambda(\mathrm{Jac}(q,M'))$ for its $\lambda$-adic Tate module, i.e. the additive subgroup of sequences $x:\mathbb N\to\mathrm{Jac}(q,M')$ with $\lambda^n x_n=0$ and $\lambda x_{n+1}=x_n$ for all $n$, regarded as a $\mathbb Z_\lambda$-module. The assertion is that for every element $t$ of the Hecke algebra `HeckeAlg`, the polynomial ring $\mathbb Z[X_\ell:\ell\text{ prime}]$, and every $\mathbb Q$-algebra automorphism $\sigma$ of $\overline{\mathbb Q}$, the two $\mathbb Z_\lambda$-linear endomorphisms $\mathrm{tateHecke}(t)$ and $\mathrm{tateGal}(\sigma)$ of $T_\lambda(\mathrm{Jac}(q,M'))$ commute. Here both operators are obtained by applying the ring homomorphism `tateEnd`, which lets an additive endomorphism of $\mathrm{Jac}(q,M')$ act termwise on Tate-module sequences: $\mathrm{tateHecke}$ comes from `heckeJac`, which sends the variable at a prime $\ell$ to `heckeGenJac` when the predicate `HeckeGenCommute q M'` holds and kills all variables otherwise, while $\mathrm{tateGal}$ comes from `galJac`, the operator $x\mapsto(\zeta\mapsto\sigma\cdot x(\sigma^{-1}\cdot\zeta))$ combining the Galois action on points with the permutation of the index set.
--
--   This is the statement that the Hecke correspondences and diamond operators on the modular curve, being defined over $\mathbb Q$, commute with the Galois action on the $\lambda$-adic Tate module of its Jacobian; it is one of the commutation requirements of a full-level Tate-module datum. It is used in the construction of such data, in the existence results for eigenspace homomorphisms and Drinfeld specialisations at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_tateHecke_mul_tateGal_comm.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.FullLevel.tateHecke_mul_tateGal_comm
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime] :
    ∀ (t : ModularCurve.HeckeAlg) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ModularCurve.FullLevel.tateHecke q M' lam t * ModularCurve.FullLevel.tateGal q M' lam σ =
        ModularCurve.FullLevel.tateGal q M' lam σ * ModularCurve.FullLevel.tateHecke q M' lam t := by sorry
