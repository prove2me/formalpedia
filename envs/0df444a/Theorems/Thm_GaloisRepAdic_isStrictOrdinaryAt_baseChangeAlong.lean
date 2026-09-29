-- Prove2me | Theorems.Thm_GaloisRepAdic_isStrictOrdinaryAt_baseChangeAlong
-- name    : GaloisRepAdic.isStrictOrdinaryAt_baseChangeAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/f265eccb-dc94-522f-ac1e-aa16fb987e10
-- title:
--   Strict ordinarity at p is preserved by local base change
-- statement:
--   Let $A$ and $B$ be commutative local rings, let $\varphi\colon A\to B$ be a ring homomorphism which is local (non-units go to non-units), and let $\rho$ be an object of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16): a free finite $A$-module $V$ with $\operatorname{rank}_A V=2$, together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)=\overline{\mathbb Q}\simeq_{\mathbb Q}\overline{\mathbb Q}$ to $\mathrm{End}_A V$ satisfying the adic continuity condition [`GaloisActionIsAdicContinuous`](def/GaloisRep_Adic.html#L9). Let $p$ be a natural number and assume `ρ.IsStrictOrdinaryAt p`, that is: $p\cdot 1\in\mathfrak m_A$, and for every valuation subring $P$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $P$ there is an $A$-submodule $L\subseteq V$ of the form $A\cdot b_0$ for some $A$-basis $b$ of $V$ indexed by $\mathrm{Fin}\,2$, such that $L$ is stable under the decomposition subgroup of $P$, such that $\rho(\sigma)v-v\in L$ for all $v\in V$ and all $\sigma$ in the image of the inertia subgroup in the decomposition subgroup, and such that every $\sigma$ in the decomposition subgroup admits $x,z\in A$ with $\rho(\sigma)w=x\,w$ for $w\in L$, $\rho(\sigma)v-z\,v\in L$ for all $v\in V$, and $x-a z\in (p^n)$ whenever $\sigma\mu=\mu^{a}$ for every $p^n$-th root of unity $\mu$. The conclusion is that the base change `ρ.baseChangeAlong φ hφ`, namely $B\otimes_A V$ with $\sigma$ acting by $\rho(\sigma)\otimes\mathrm{id}$, satisfies `IsStrictOrdinaryAt p` over $B$.
--
--   This is the change-of-coefficients compatibility for Wiles's strict ordinary deformation condition at $p$: the condition that the decomposition group preserves a free rank-one line on which it acts by the cyclotomic character times the character giving its action on the quotient. It is one of the axioms making that condition a deformation condition, and it is used when transporting strict ordinarity along ring homomorphisms between local Hecke-algebra-type coefficient rings, for instance in the construction of patching data and in the passage from a Hecke algebra to its local quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isStrictOrdinaryAt_baseChangeAlong.lean

import Definitions.Def_GaloisRep_StrictOrdinary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isStrictOrdinaryAt_baseChangeAlong
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {p : ℕ} (h : ρ.IsStrictOrdinaryAt p) : (ρ.baseChangeAlong φ hφ).IsStrictOrdinaryAt p := by sorry
