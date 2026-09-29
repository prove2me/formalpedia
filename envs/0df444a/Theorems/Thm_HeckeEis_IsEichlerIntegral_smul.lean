-- Prove2me | Theorems.Thm_HeckeEis_IsEichlerIntegral_smul
-- name    : HeckeEis.IsEichlerIntegral.smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/e54577d3-520a-5111-8302-693dd938b73e
-- title:
--   Eichler integrals scale: cF is an Eichler integral of cf
-- statement:
--   Let $n$ be a natural number, let $f:\mathfrak H\to\mathbb C$ be a function on the upper half-plane, and let $F$ be a function from $\mathfrak H$ to the submodule $\mathrm{BinaryForm}\ \mathbb C\ n$ of $\mathbb C[X_0,X_1]$ consisting of the homogeneous polynomials of degree $n$ in two variables. Assume $F$ is an Eichler integral of $f$ in the sense of [`HeckeEis.IsEichlerIntegral`](def/HeckeEis_EichlerIntegral.html#L105): for every multi-index $d\in(\mathrm{Fin}\,2\to_0\mathbb N)$ and every $\tau\in\mathfrak H$, the complex function $z\mapsto \mathrm{coeff}_d\bigl(F(\mathrm{ofComplex}\,z)\bigr)$ is differentiable at the point $\tau\in\mathbb C$ with derivative $f(\tau)\cdot \mathrm{coeff}_d\bigl((\tau X_0+X_1)^n\bigr)$, where $(\tau X_0+X_1)^n$ is [`HeckeEis.linePow n τ`](def/HeckeEis_EichlerIntegral.html#L22) and `ofComplex` is the retraction of $\mathbb C$ onto $\mathfrak H$. Then for every scalar $c\in\mathbb C$ the pointwise multiple $c\cdot F$ is an Eichler integral of $c\cdot f$ in the same sense, i.e. the relation $d(cF)=(cf)(\tau)(\tau X_0+X_1)^n\,d\tau$ holds coefficientwise in the above derivative form.
--
--   This is the homogeneity half of the linearity of the Eichler integral relation, recorded coefficientwise for polynomial-valued primitives. It is used for the scalar-homogeneity of the Eichler–Shimura map, [`HeckeEis.eichlerShimuraMap_smul`](thm.html#HeckeEis.eichlerShimuraMap_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_IsEichlerIntegral_smul.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.smul {n : ℕ} {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (c : ℂ) :
    HeckeEis.IsEichlerIntegral n (c • f) (c • F) := by sorry
