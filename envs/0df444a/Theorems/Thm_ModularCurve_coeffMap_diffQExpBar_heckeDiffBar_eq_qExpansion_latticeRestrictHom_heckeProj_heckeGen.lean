-- Prove2me | Theorems.Thm_ModularCurve_coeffMap_diffQExpBar_heckeDiffBar_eq_qExpansion_latticeRestrictHom_heckeProj_heckeGen
-- name    : ModularCurve.coeffMap_diffQExpBar_heckeDiffBar_eq_qExpansion_latticeRestrictHom_heckeProj_heckeGen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/7685de2a-4922-5bf0-b261-6cfa948077a9
-- title:
--   Hecke correspondence on differentials matches the Hecke operator on q-expansions
-- statement:
--   Fix $N\ge 1$, a ring homomorphism $\iota_0\colon \overline{\mathbf Q}\to\mathbf C$ from the algebraic closure of $\mathbf Q$ used in the project, and a prime $\ell$. Let $\bar F_N$ denote `modularFunctionFieldBar N`, the base change to $\overline{\mathbf Q}$ of the full modular function field of level $N$ inside $\overline{\mathbf Q}((q))$, let $\eta$ be a Kähler differential of $\bar F_N$ over $\overline{\mathbf Q}$, and write $\mathrm{diffQExpBar}\,N$ for the $\bar F_N$-linear map $\Omega_{\bar F_N/\overline{\mathbf Q}}\to\overline{\mathbf Q}((q))$ obtained from the $q$-Euler derivation by the universal property of the module of Kähler differentials. Let $f$ be an element of [`CuspForm.intLattice N 2`](def/CuspForm_IntegralStructure.html#L3), the $\mathbf Z$-submodule of weight-two cusp forms on $\Gamma_0(N)$ spanned by those all of whose $q$-expansion coefficients are rational integers. Assume that the Laurent series $\mathrm{diffQExpBar}\,N\,\eta$, pushed forward coefficientwise along $\iota_0$, equals the Laurent series attached to the power series $q$-expansion (period $1$) of $f$. The conclusion is the same identity with $\eta$ replaced by $\mathrm{heckeDiffBar}\,N\,\ell\,\eta$, the image of $\eta$ under the correspondence built from the two maps $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ at $\ell$, and $f$ replaced by the image of $f$ under the endomorphism of the lattice obtained by sending the polynomial generator $X_\ell$ of $\mathbf Z[X_p : p\ \text{prime}]$ to $U_\ell$ if $\ell\mid N$ and to $T_\ell$ otherwise, and restricting that element of the weight-two Hecke algebra to [`CuspForm.intLattice N 2`](def/CuspForm_IntegralStructure.html#L3).
--
--   This is the compatibility, through $q$-expansions, between the Hecke correspondence on differentials of the modular curve of level $N$ over $\overline{\mathbf Q}$ and the Hecke operators $T_\ell$ ($\ell\nmid N$), $U_\ell$ ($\ell\mid N$) on the integral lattice of weight-two cusp forms for $\Gamma_0(N)$. It is used in the construction of a Hecke-equivariant comparison isomorphism between the space of regular differentials over $\overline{\mathbf Q}$ and the base change of that lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeffMap_diffQExpBar_heckeDiffBar_eq_qExpansion_latticeRestrictHom_heckeProj_heckeGen.lean

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CuspForm

theorem ModularCurve.coeffMap_diffQExpBar_heckeDiffBar_eq_qExpansion_latticeRestrictHom_heckeProj_heckeGen
    (N : ℕ) [NeZero N] (ι₀ : AlgebraicClosure ℚ →+* ℂ) (ℓ : Nat.Primes)
    (η : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ]) (f : ↥(CuspForm.intLattice N 2))
    (h : coeffMap ι₀ (diffQExpBar N η) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2))) :
    coeffMap ι₀ (diffQExpBar N (heckeDiffBar N ℓ η)) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1
        (((((CuspForm.latticeRestrictHom N ∅).toRingHom.comp (heckeProj N)) (heckeGen ℓ)).val f :
            ↥(CuspForm.intLattice N 2)) : CuspForm (CongruenceSubgroup.Gamma0 N) 2)) := by sorry
