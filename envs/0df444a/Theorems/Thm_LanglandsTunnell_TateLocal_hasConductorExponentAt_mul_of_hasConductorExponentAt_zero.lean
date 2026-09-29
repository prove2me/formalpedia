-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_zero
-- name    : LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/a81b8719-33c2-571c-8c80-d4dfcd8d9f14
-- title:
--   Conductor exponent is invariant under unramified twist
-- statement:
--   Let $K$ be a number field and let $v$ be a height-one prime of its ring of integers, so that $K_v$ denotes the corresponding $v$-adic completion, equipped with its valuation. For $n \in \mathbb{N}$ write $U^{(n)}$ for the set `higherUnitsAt K v n` of units $u$ of $K_v$ with $\mathrm{v}(u) = 1$ and such that either $n = 0$ or $\mathrm{v}(u - 1) \le \exp(-n)$. Say that a monoid homomorphism $\psi \colon K_v^\times \to \mathbb{C}^\times$ has conductor exponent $c \in \mathbb{N}$, written `HasConductorExponentAt K v`$\ \psi\ c$, when $\psi(u) = 1$ for all $u \in U^{(c)}$ and, for every $m < c$, there exists $u \in U^{(m)}$ with $\psi(u) \ne 1$. Given two monoid homomorphisms $\chi, \omega \colon K_v^\times \to \mathbb{C}^\times$ and a natural number $c$ such that $\chi$ has conductor exponent $c$ and $\omega$ has conductor exponent $0$, the theorem asserts that the pointwise product $\chi \cdot \omega$ again has conductor exponent $c$.
--
--   This is the statement that the conductor exponent of a quasi-character of $K_v^\times$ is unchanged on twisting by an unramified quasi-character, in the sharp form in which the exponent is characterised by triviality on $U^{(c)}$ together with non-triviality on each $U^{(m)}$, $m < c$. It is used, with the companion law for Tate's local root number, in the computation of local constants for characters induced from quadratic and cubic extensions, and hence in the inductivity statements and the dihedral cases of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_zero.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain

theorem LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_zero
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (χ ω : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ) (hχ : HasConductorExponentAt K v χ c)
    (hω : HasConductorExponentAt K v ω 0) :
    HasConductorExponentAt K v (χ * ω) c := by sorry
