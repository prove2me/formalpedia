-- Prove2me | Theorems.Thm_HeckeEis_exists_isEichlerIntegral
-- name    : HeckeEis.exists_isEichlerIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/5099303c-73dd-5949-90e0-b6c69197a54e
-- title:
--   Existence of Eichler integrals for holomorphic functions on H
-- statement:
--   Fix a natural number $n$ and a function $f$ on the upper half-plane $\mathfrak H$ with values in $\mathbb C$ which is holomorphic in the sense of being $\mathrm{MDifferentiable}$ for the model with corners $\mathcal I(\mathbb C)$ on source and target. The assertion is that there exists a function $F$ on $\mathfrak H$ with values in the submodule [`HeckeEis.BinaryForm ℂ n`](def/HeckeEis_BinaryFormRep.html#L25) of $\mathbb C$-valued polynomials in two variables $X_0, X_1$ which are homogeneous of degree $n$, such that [`HeckeEis.IsEichlerIntegral n f F`](def/HeckeEis_EichlerIntegral.html#L105) holds. Unfolded, the latter says: for every exponent vector $d : \mathrm{Fin}\,2 \to_0 \mathbb N$ and every $\tau \in \mathfrak H$, the complex function $z \mapsto \operatorname{coeff}_d\bigl(F(\mathrm{ofComplex}\,z)\bigr)$, defined on all of $\mathbb C$ via the retraction $\mathrm{ofComplex} : \mathbb C \to \mathfrak H$, has derivative at the point $\tau$ equal to $f(\tau)\cdot \operatorname{coeff}_d\bigl((\tau X_0 + X_1)^n\bigr)$, where $(\tau X_0+X_1)^n$ is [`HeckeEis.linePow n τ`](def/HeckeEis_EichlerIntegral.html#L22). Thus $F$ is, coefficient by coefficient, a primitive of the $\operatorname{Sym}^n$-valued function $\tau \mapsto f(\tau)(\tau X_0+X_1)^n$, with the derivative condition recorded in the strong form of `HasDerivAt` at every point of $\mathfrak H$.
--
--   This is the existence statement for Eichler integrals in weight $n+2$: a holomorphic function on $\mathfrak H$ admits a $\operatorname{Sym}^n(\mathbb C^2)$-valued primitive of $f(\tau)(\tau X_0+X_1)^n$. It is the purely analytic input to the Eichler–Shimura construction, used downstream to attach (parabolic) cocycles to modular forms and to compare Hecke actions on cohomology with Hecke actions on forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_isEichlerIntegral.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold MatrixGroups

theorem HeckeEis.exists_isEichlerIntegral (n : ℕ) {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ∃ F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n), HeckeEis.IsEichlerIntegral n f F := by sorry
