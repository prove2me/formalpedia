-- Prove2me | Theorems.Thm_ModularCurve_mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel
-- name    : ModularCurve.mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/26d88eb3-f5d8-5fcb-a55a-1e3aa5fb8e1d
-- title:
--   Galois action on 𝔪-torsion of J₀(M) factors through a finite level
-- statement:
--   Let $M$ be a natural number, nonzero, and let $\mathfrak{m}$ be an ideal of the Hecke algebra `HeckeAlg`, which here is the polynomial ring $\mathbb{Z}[T_\ell : \ell \text{ prime}]$ on the set of primes. Write $J_0(M)$ for `JZero M`, the group $\mathrm{Pic}^0$ of the function field of the modular curve of level $M$ base-changed to $\overline{\mathbb{Q}}$, i.e. degree-zero divisors modulo principal divisors, equipped with its action of $G=\overline{\mathbb{Q}}\simeq_{\mathbb{Q}}\overline{\mathbb{Q}}$ and with the `HeckeAlg`-module structure `heckeModuleBar M`. Two hypotheses are assumed for that module structure: that the $G$-action and the `HeckeAlg`-action on $J_0(M)$ commute, and that the $\mathfrak{m}$-torsion submodule $\{x : a \cdot x = 0 \text{ for all } a \in \mathfrak{m}\}$ is finite. The conclusion is that the monoid homomorphism `mTorsionGaloisRep`, sending $\sigma \in G$ to the `HeckeAlg`$/\mathfrak{m}$-linear endomorphism $x \mapsto \sigma \cdot x$ of that $\mathfrak{m}$-torsion submodule, satisfies [`GaloisFactorsThroughFiniteLevel`](def/GaloisRep_Residual.html#L17): there is an intermediate field $L$ between $\mathbb{Q}$ and $\overline{\mathbb{Q}}$, finite-dimensional over $\mathbb{Q}$, such that every $\sigma$ fixing $L$ pointwise is sent to the identity endomorphism.
--
--   This is the continuity input for the Galois representations attached to ideals of the Hecke algebra: the action on a finite $\mathfrak{m}$-torsion subgroup of the modular Jacobian is unramified outside a finite level, so that it may be treated as a representation of a finite Galois group. It is used downstream in the analysis of such residual representations, for instance in the determinant computations on the $\mathfrak{m}$-torsion of $J_0(M)$ and in the construction of stable lines.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_JZeroTorsionFinite
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve

theorem ModularCurve.mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel (M : ℕ) [NeZero M]
    (𝔪 : Ideal HeckeAlg)
    (hsmc : letI := heckeModuleBar M
      SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero M))
    (hfin : letI := heckeModuleBar M; Finite (heckeTorsion (JZero M) 𝔪)) :
    letI := heckeModuleBar M; haveI := hsmc
    GaloisFactorsThroughFiniteLevel
      (mTorsionGaloisRep (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero M) 𝔪) := by sorry
