-- Prove2me | Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffParabolicCocycles
-- name    : HeckeEis.coeffHeckeFun_mem_coeffParabolicCocycles
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/600d226f-3cc9-5bc7-917a-bc0a0e9e5854
-- title:
--   Hecke operator preserves parabolic cocycles with coefficients
-- statement:
--   Let $N$ and $\ell$ be natural numbers with $\ell \neq 0$, let $K$ be a commutative ring, let $V$ be a $K$-module and let $\rho$ be a $K$-linear representation of $\Gamma_0(N) \le \mathrm{SL}(2,\mathbb{Z})$ on $V$. Write $\mathrm{heckeUpper}\,N\,\ell$ for the subgroup of $\Gamma_0(N)$ consisting of those matrices whose upper right entry is divisible by $\ell$, and $\mathrm{heckeConj}\,N\,\ell$ for the homomorphism from it to $\Gamma_0(N)$ sending $g$ to $!![g_{00}, g_{01}/\ell; \ell\, g_{10}, g_{11}]$, i.e. conjugation by $\mathrm{diag}(1,\ell)$. Let $a : V \to V$ be $K$-linear and assume $a \circ \rho(\mathrm{heckeConj}\,N\,\ell\,u) = \rho(u) \circ a$ for every $u \in \mathrm{heckeUpper}\,N\,\ell$. Let $z : \Gamma_0(N) \to V$ be a parabolic $1$-cocycle, that is: $z(gh) = z(g) + \rho(g)(z(h))$ for all $g,h$, and $z(\gamma) \in \mathrm{range}(\rho(\gamma) - 1)$ for every $\gamma \in \Gamma_0(N)$ whose underlying integral matrix satisfies $(\operatorname{tr}\gamma)^2 = 4$. Then the function $\mathrm{coeffHeckeFun}\,N\,\ell\,\rho\,a\,z$, whose value at $g$ is the sum over the (finitely many) cosets $q \in \Gamma_0(N)/\mathrm{heckeUpper}\,N\,\ell$ of $\rho((g \cdot q)^{\mathrm{out}})\bigl(a\bigl(z(\mathrm{heckeConj}\,N\,\ell\,((g\cdot q)^{\mathrm{out}})^{-1} g\, q^{\mathrm{out}})\bigr)\bigr)$ with $q^{\mathrm{out}}$ the chosen coset representative, is again a parabolic $1$-cocycle.
--
--   This is the cochain-level statement that the Hecke correspondence at $\ell$, with coefficients twisted by the intertwining map $a$, acts on parabolic cocycles of $\Gamma_0(N)$, so that it descends to parabolic cohomology; the underlying cocycle property alone is [`HeckeEis.coeffHeckeFun_mem_coeffCocycles`](thm.html#HeckeEis.coeffHeckeFun_mem_coeffCocycles), and the content added here is the parabolicity condition at elements of trace $\pm 2$. It is used in the construction of the Hecke action on $H^1_{\mathrm{par}}$ and in the passage from eigensystems in cohomology to modular forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_coeffHeckeFun_mem_coeffParabolicCocycles.lean

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.coeffHeckeFun_mem_coeffParabolicCocycles (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ HeckeEis.coeffParabolicCocycles ρ) :
    HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ HeckeEis.coeffParabolicCocycles ρ := by sorry
