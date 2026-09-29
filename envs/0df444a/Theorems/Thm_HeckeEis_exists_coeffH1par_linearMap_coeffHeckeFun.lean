-- Prove2me | Theorems.Thm_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun
-- name    : HeckeEis.exists_coeffH1par_linearMap_coeffHeckeFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/5687e012-801a-55f3-80ae-d7d0dbe45568
-- title:
--   Existence of the induced Hecke endomorphism of H¹ₚₐᵣ
-- statement:
--   Fix natural numbers $N$ and $\ell$ with $\ell \neq 0$, a commutative ring $K$, a $K$-module $V$, a representation $\rho$ of the group $\Gamma_0(N)$ on $V$ over $K$, and a $K$-linear endomorphism $a$ of $V$. Assume the intertwining hypothesis: for every $u$ in [`HeckeEis.heckeUpper N ℓ`](def/Gamma0HeckeOperatorHom.html#L128), the subgroup of those elements of $\Gamma_0(N)$ whose upper right entry is divisible by $\ell$, one has $a \circ \rho(\mathrm{heckeConj}(u)) = \rho(u) \circ a$, where $\mathrm{heckeConj}(u)$ is the matrix obtained from $u = \begin{pmatrix} \alpha & \beta \\ \gamma & \delta\end{pmatrix}$ as $\begin{pmatrix} \alpha & \beta/\ell \\ \gamma\ell & \delta\end{pmatrix}$ (conjugation by $\mathrm{diag}(1,\ell)$), viewed again in $\Gamma_0(N)$. The conclusion asserts the existence of a $K$-linear endomorphism $T$ of [`HeckeEis.coeffH1par ρ`](def/Gamma0CoeffCohomology.html#L100) — the quotient of the submodule of parabolic cocycles (functions $z : \Gamma_0(N) \to V$ with $z(gh) = z(g) + \rho(g)z(h)$ and $z(\gamma) \in \mathrm{im}(\rho(\gamma) - 1)$ whenever the integral matrix $\gamma$ has $\mathrm{tr}(\gamma)^2 = 4$) by the parabolic cocycles that are coboundaries — such that for every parabolic cocycle $z$ there is a parabolic cocycle $w$ whose underlying function $\Gamma_0(N) \to V$ equals [`HeckeEis.coeffHeckeFun N ℓ ρ a z`](def/Gamma0CoeffCohomology.html#L129), the finite sum over $q \in \Gamma_0(N)/\mathrm{heckeUpper}(N,\ell)$ of $\rho((g\cdot q)^{\mathrm{out}})\bigl(a\,z(\mathrm{heckeConj}(\mathrm{transferAux}(g,q)))\bigr)$, and such that $T$ sends the class of $z$ to the class of $w$. Thus the statement simultaneously records that the cochain-level operator preserves parabolic cocycles and that it descends to the quotient.
--
--   This is the construction of the Hecke operator $T_\ell$ on the parabolic cohomology $H^1_{\mathrm{par}}(\Gamma_0(N), \rho)$ from its cochain-level avatar, in the classical Eichler–Shimura setting where the coefficient datum is a linear map $a$ intertwining $\rho$ with its conjugate by $\mathrm{diag}(1,\ell)$. It is used in the construction of Hecke eigenclasses in parabolic cohomology of binary-form representations and, through those, in the integral-structure statement for cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun.lean

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_coeffH1par_linearMap_coeffHeckeFun (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a) :
    ∃ T : HeckeEis.coeffH1par ρ →ₗ[K] HeckeEis.coeffH1par ρ,
      ∀ z : ↥(HeckeEis.coeffParabolicCocycles ρ), ∃ w : ↥(HeckeEis.coeffParabolicCocycles ρ),
        (w : CongruenceSubgroup.Gamma0 N → V) = HeckeEis.coeffHeckeFun N ℓ ρ a z ∧
          T (HeckeEis.coeffH1parMk ρ z) = HeckeEis.coeffH1parMk ρ w := by sorry
