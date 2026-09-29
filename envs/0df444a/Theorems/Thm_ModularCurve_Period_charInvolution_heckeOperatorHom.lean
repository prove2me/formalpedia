-- Prove2me | Theorems.Thm_ModularCurve_Period_charInvolution_heckeOperatorHom
-- name    : ModularCurve.Period.charInvolution_heckeOperatorHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/b8245fd1-3245-5a05-aaac-8defbde38af6
-- title:
--   Hecke operators commute with the character involution on Γ₀(N)
-- statement:
--   Let $N$ and $\ell$ be natural numbers with $\ell \neq 0$, let $A$ be an additive abelian group, and let $\varphi \colon \mathrm{Additive}\,\Gamma_0(N) \to A$ be an additive homomorphism, i.e. a group homomorphism from $\Gamma_0(N)$ to $A$. Two operations on such $\varphi$ are involved. First, [`ModularCurve.Period.charInvolution N ℤ A`](def/ModularCurve_PeriodHomPair.html#L95) is the $\mathbb{Z}$-linear map sending $\varphi$ to its precomposition with `jConjGamma0 N`, the endomorphism of $\Gamma_0(N)$ obtained by applying `jConjSL` to the underlying element of $\mathrm{SL}_2(\mathbb{Z})$ (which preserves $\Gamma_0(N)$). Second, [`HeckeEis.heckeOperatorHom N ℓ A`](def/Gamma0HeckeOperatorHom.html#L285) is the composite of precomposition with the homomorphism `heckeConj N ℓ` from `heckeUpper N ℓ` — the subgroup of $\Gamma_0(N)$ consisting of those elements lying in `heckeUpperSL ℓ` — to $\Gamma_0(N)$, given on matrices by `heckeConjMat ℓ`, followed by the transfer (corestriction) map `coresHom`, which sends a homomorphism $\psi$ on `heckeUpper N ℓ` to $g \mapsto \sum_{q \in \Gamma_0(N)/\text{heckeUpper } N\,\ell} \psi(\mathrm{transferAux}\, g\, q)$. The assertion is that these two operators commute on $\varphi$: applying the character involution to `heckeOperatorHom N ℓ A φ` gives the same homomorphism as applying `heckeOperatorHom N ℓ A` to the character involution of $\varphi$. No condition relating $\ell$ to $N$ is imposed, so the statement covers both the $T_\ell$ and the $U_\ell$ cases.
--
--   This is the compatibility of the $J$-conjugation character involution on $\mathrm{Hom}(\Gamma_0(N), A)$ with the Hecke operators defined by transfer along the upper-triangular Hecke subgroup, at every nonzero level parameter $\ell$. It feeds into the Hecke-equivariance of the period homomorphism pair and is used in the construction of the Eichler–Shimura comparison for $H^1$ and in the associated statements about the Hecke algebra acting on parabolic homomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_Period_charInvolution_heckeOperatorHom.lean

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodHomPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.Period.charInvolution_heckeOperatorHom (N ℓ : ℕ) [NeZero ℓ]
    (A : Type*) [AddCommGroup A] (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ A) :
    ModularCurve.Period.charInvolution N ℤ A (HeckeEis.heckeOperatorHom N ℓ A φ)
      = HeckeEis.heckeOperatorHom N ℓ A (ModularCurve.Period.charInvolution N ℤ A φ) := by sorry
