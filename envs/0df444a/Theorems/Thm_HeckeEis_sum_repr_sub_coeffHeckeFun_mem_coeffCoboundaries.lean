-- Prove2me | Theorems.Thm_HeckeEis_sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries
-- name    : HeckeEis.sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/89330c6b-b618-5bc1-bb62-803cfcb9a592
-- title:
--   Hecke cochain is representative-independent modulo coboundaries
-- statement:
--   Fix natural numbers $N$ and $\ell$ with $\ell \neq 0$, a commutative ring $K$, a $K$-module $V$, a representation $\rho$ of $\Gamma_0(N)$ on $V$ over $K$, and a $K$-linear endomorphism $a$ of $V$. Write $U =$ [`HeckeEis.heckeUpper N ℓ`](def/Gamma0HeckeOperatorHom.html#L128) for the subgroup of $\Gamma_0(N)$ consisting of those matrices whose upper-right entry is divisible by $\ell$, and [`HeckeEis.heckeConj N ℓ`](def/Gamma0HeckeOperatorHom.html#L172) for the group homomorphism $U \to \Gamma_0(N)$ sending $\begin{pmatrix} a & b \\ c & d\end{pmatrix}$ to $\begin{pmatrix} a & b/\ell \\ c\ell & d\end{pmatrix}$. Assume the intertwining relation $a \circ \rho(\mathrm{heckeConj}(u)) = \rho(u) \circ a$ for every $u \in U$. Let $s \colon \Gamma_0(N)/U \to \Gamma_0(N)$ be any set-theoretic section, i.e. $s(q)$ lies in the coset $q$ for all $q$, and let $t \colon \Gamma_0(N) \times (\Gamma_0(N)/U) \to U$ satisfy the transfer identity $s(g \cdot q)\, t(g,q) = g\, s(q)$ for all $g$ and $q$. Let $z \colon \Gamma_0(N) \to V$ be a $1$-cocycle, i.e. $z(gh) = z(g) + \rho(g)(z(h))$ for all $g,h$. Then the function $$g \mapsto \sum_{q \in \Gamma_0(N)/U} \rho\bigl(s(g\cdot q)\bigr)\bigl(a\bigl(z(\mathrm{heckeConj}(t(g,q)))\bigr)\bigr)$$ (the sum being finite, $U$ having finite index in $\Gamma_0(N)$) differs from [`HeckeEis.coeffHeckeFun N ℓ ρ a z`](def/Gamma0CoeffCohomology.html#L129), which is the same sum taken with $s(q)$ replaced by the canonical representative $q.\mathrm{out}$ and $t(g,q)$ by $(g\cdot q).\mathrm{out}^{-1}(g\, q.\mathrm{out})$, by a $1$-coboundary: the difference lies in the image of the map $v \mapsto (g \mapsto \rho(g)v - v)$.
--
--   This is the coefficient analogue of the representative-independence of the transfer (corestriction) cochain: the Hecke cochain built from an arbitrary system of coset representatives for $U$ in $\Gamma_0(N)$ represents the same class in $H^1(\Gamma_0(N), \rho)$ as the one built from the canonical representatives. It is used to compose Hecke operators at cochain level, to identify the induced operator with the classical Hecke operator on modular symbols, and to compare Hecke actions after a change of group, where representatives are chosen adapted to a smaller congruence subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries.lean

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    (s : CongruenceSubgroup.Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ → CongruenceSubgroup.Gamma0 N)
    (t : CongruenceSubgroup.Gamma0 N → CongruenceSubgroup.Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ →
      ↥(HeckeEis.heckeUpper N ℓ))
    (hs : ∀ q, (s q : CongruenceSubgroup.Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ) = q)
    (hst : ∀ g q, s (g • q) * (t g q : CongruenceSubgroup.Gamma0 N) = g * s q)
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ HeckeEis.coeffCocycles ρ) :
    (fun g => letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
        ∑ q : CongruenceSubgroup.Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ,
          ρ (s (g • q)) (a (z (HeckeEis.heckeConj N ℓ (t g q)))))
      - HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ HeckeEis.coeffCoboundaries ρ := by sorry
