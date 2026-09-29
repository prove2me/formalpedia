-- Prove2me | Theorems.Thm_HeckeEis_eichlerShimuraMap_eq_coeffH1parMk
-- name    : HeckeEis.eichlerShimuraMap_eq_coeffH1parMk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/c45b784f-df99-52af-9e4f-b91b69432be5
-- title:
--   Eichler–Shimura map computed by any admissible Eichler integral
-- statement:
--   Fix natural numbers $n$ and $N$ and a function $f\colon\mathfrak H\to\mathbb C$ on the upper half-plane, and let $V_n =$ [`HeckeEis.BinaryForm ℂ n`](def/HeckeEis_BinaryFormRep.html#L25) be the space of homogeneous polynomials of degree $n$ in two variables $X_0,X_1$ over $\mathbb C$, on which $\rho$ denotes the representation `(HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype`, i.e. $\mathrm{SL}_2(\mathbb Z)$ acting by the linear substitution $X_j\mapsto\sum_i M_{ij}X_i$, restricted to $\Gamma_0(N)$. Let $F\colon\mathfrak H\to V_n$ satisfy three hypotheses: (i) $F$ is an Eichler integral of $f$, meaning that for every exponent $d$ and every $\tau\in\mathfrak H$ the coefficient function $z\mapsto \mathrm{coeff}_d(F(z))$ has complex derivative $f(\tau)\,\mathrm{coeff}_d\big((\tau X_0+X_1)^n\big)$ at $\tau$; (ii) $F$ is an equivariant primitive for $\rho$, i.e. for each $\gamma\in\Gamma_0(N)$ the function $\tau\mapsto F(\gamma\tau)-\rho(\gamma)F(\tau)$ is a constant of $V_n$; (iii) the associated cocycle $z_F(\gamma)=F(\gamma\cdot i)-\rho(\gamma)F(i)$ is parabolic, i.e. $z_F(\gamma)\in\mathrm{range}(\rho(\gamma)-1)$ whenever $\mathrm{tr}(\gamma)^2=4$. The conclusion is that [`HeckeEis.eichlerShimuraMap n N f`](def/HeckeEis_EichlerIntegral.html#L114), defined by choosing some such $F$ when one exists and $0$ otherwise, equals the class of $z_F$ in [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100), the quotient of the module of parabolic cocycles by those which are coboundaries.
--
--   This identifies the Eichler–Shimura class attached to $f$ with the cohomology class of the cocycle of any Eichler integral of $f$ that is an equivariant primitive with parabolic cocycle, so that the choice implicit in the definition is immaterial. It is the computational entry point for the additivity and Hecke-compatibility statements about the Eichler–Shimura map, being cited by [`HeckeEis.eichlerShimuraMap_add`](thm.html#HeckeEis.eichlerShimuraMap_add), [`HeckeEis.eichlerShimuraMap_heckeTLin`](thm.html#HeckeEis.eichlerShimuraMap_heckeTLin) and [`HeckeEis.eichlerShimuraMap_heckeULin`](thm.html#HeckeEis.eichlerShimuraMap_heckeULin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_eichlerShimuraMap_eq_coeffH1parMk.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem HeckeEis.eichlerShimuraMap_eq_coeffH1parMk (n N : ℕ) (f : UpperHalfPlane → ℂ)
    {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hEI : HeckeEis.IsEichlerIntegral n f F)
    (hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F)
    (hpar : HeckeEis.IsParabolicCocycle
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) hF.cocycle) :
    HeckeEis.eichlerShimuraMap n N f
      = HeckeEis.coeffH1parMk _ ⟨hF.cocycle, ⟨hF.cocycle_mem_coeffCocycles, hpar⟩⟩ := by sorry
