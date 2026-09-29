-- Prove2me | Theorems.Thm_HeckeEis_IsEichlerIntegral_slash
-- name    : HeckeEis.IsEichlerIntegral.slash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/bacf79e5-40a4-5112-a663-bfd1e4b2124b
-- title:
--   Eichler integrals transform under SL₂(ℤ)
-- statement:
--   Fix a natural number $n$, a function $f$ on the upper half-plane with values in $\mathbb C$, and a function $F$ from the upper half-plane to the submodule $\mathrm{BinaryForm}\ \mathbb C\ n$ of binary forms of degree $n$, i.e. the homogeneous polynomials of degree $n$ in $\mathbb C[X_0,X_1]$. Assume [`HeckeEis.IsEichlerIntegral n f F`](def/HeckeEis_EichlerIntegral.html#L105), which says: for every multidegree $d \in (\mathrm{Fin}\,2 \to_0 \mathbb N)$ and every $\tau$ in the upper half-plane, the function $z \mapsto \mathrm{coeff}_d\,F(\mathrm{ofComplex}\,z)$ on $\mathbb C$ has complex derivative $f(\tau)\cdot \mathrm{coeff}_d\bigl((\tau X_0 + X_1)^n\bigr)$ at the point $\tau$. Let $\delta \in \mathrm{SL}(2,\mathbb Z)$. The conclusion is that the same predicate holds for the pair consisting of the weight-$((n:\mathbb Z)+2)$ slash $f \mid[(n:\mathbb Z)+2]\ \delta$ and the function $\tau \mapsto \rho_n(\delta^{-1})\,F(\delta \cdot \tau)$, where $\rho_n =$ [`HeckeEis.binaryFormRepSL ℂ n`](def/HeckeEis_BinaryFormRep.html#L61) is the representation of $\mathrm{SL}(2,\mathbb Z)$ on degree-$n$ binary forms by the substitution $X_j \mapsto \sum_i g_{ij} X_i$: that is, coefficientwise, $z \mapsto \mathrm{coeff}_d\,\rho_n(\delta^{-1})F(\delta\cdot \mathrm{ofComplex}\,z)$ has derivative $(f\mid[(n:\mathbb Z)+2]\,\delta)(\tau)\cdot\mathrm{coeff}_d((\tau X_0+X_1)^n)$ at every $\tau$.
--
--   This is the compatibility of the Eichler integral construction with the weight-$(n+2)$ slash action: twisting an Eichler integral of $f$ by $\rho_n(\delta^{-1})$ and precomposing with $\delta$ produces an Eichler integral of $f\mid[(n+2)]\delta$. It is the mechanism behind the cocycle relations used for equivariance and behaviour at the cusps in the Eichler–Shimura picture, and is invoked in the period computations, in [`HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral`](thm.html#HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral) and in the injectivity of the Eichler–Shimura map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_IsEichlerIntegral_slash.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.slash {n : ℕ} {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (δ : SL(2, ℤ)) :
    HeckeEis.IsEichlerIntegral n (f ∣[((n : ℤ) + 2)] δ) (fun τ => HeckeEis.binaryFormRepSL ℂ n δ⁻¹ (F (δ • τ))) := by sorry
