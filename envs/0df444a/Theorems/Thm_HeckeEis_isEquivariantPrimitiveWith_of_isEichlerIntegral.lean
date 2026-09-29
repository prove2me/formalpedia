-- Prove2me | Theorems.Thm_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral
-- name    : HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/daa1f7da-7620-5a5c-9047-44d2ff15d46b
-- title:
--   Eichler integrals of slash-invariant f are equivariant primitives
-- statement:
--   Fix $n \in \mathbb{N}$, a subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$, a function $f : \mathfrak{H} \to \mathbb{C}$ on the upper half-plane, and a function $F$ from $\mathfrak{H}$ to [`HeckeEis.BinaryForm ℂ n`](def/HeckeEis_BinaryFormRep.html#L25), the submodule of $\mathbb{C}[X_0,X_1]$ of forms homogeneous of degree $n$. Assume first that $F$ is an Eichler integral of $f$ in the sense of [`HeckeEis.IsEichlerIntegral`](def/HeckeEis_EichlerIntegral.html#L105): for every exponent vector $d : \mathrm{Fin}\,2 \to_0 \mathbb{N}$ and every $\tau \in \mathfrak{H}$, the function $z \mapsto \mathrm{coeff}_d\,F(z)$ (with $F$ extended to $\mathbb{C}$ by `ofComplex`) has complex derivative $f(\tau)\cdot \mathrm{coeff}_d\big((\tau X_0 + X_1)^n\big)$ at $z = \tau$. Assume second that $f \mid_{n+2} \gamma = f$ for every $\gamma \in \Gamma$, the slash action in weight $(n : \mathbb{Z}) + 2$. The conclusion is [`HeckeEis.IsEquivariantPrimitiveWith`](def/HeckeEis_EichlerIntegral.html#L68) for the restriction to $\Gamma$ of the representation `binaryFormRepSL` of $\mathrm{SL}_2(\mathbb{Z})$ on degree-$n$ binary forms, given by the substitution $X_j \mapsto \sum_i M_{ij} X_i$: for every $\gamma \in \Gamma$ there is a binary form $c$ of degree $n$ with $F(\gamma \cdot \tau) - \rho(\gamma)\,F(\tau) = c$ for all $\tau \in \mathfrak{H}$. No holomorphy or growth condition on $f$ is imposed beyond the stated invariance.
--
--   This is the first step of Eichler–Shimura theory: the period map attached to an Eichler integral, $\gamma \mapsto F(\gamma\tau) - \rho_n(\gamma)F(\tau)$, is independent of $\tau$ and so defines a cocycle on $\Gamma$ with values in $\mathrm{Sym}^n$. It is used in the construction of Eichler integrals with parabolic cocycles and in the comparison of modular forms with cohomology classes under the Hecke action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral
    {n : ℕ} {Γ : Subgroup SL(2, ℤ)} {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F)
    (hf : ∀ γ ∈ Γ, (f ∣[((n : ℤ) + 2)] γ) = f) :
    HeckeEis.IsEquivariantPrimitiveWith ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype) F := by sorry
