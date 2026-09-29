-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_finite_setOf_pinnedExp_ne_zero_of_continuous
-- name    : LanglandsTunnell.Converse.finite_setOf_pinnedExp_ne_zero_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/440565ce-a4bb-5c4c-8624-586ed2bb13d5
-- title:
--   Finiteness of the pinned exponent of a continuous idele character
-- statement:
--   Let $K$ be a number field (a field with a `NumberField` structure) and let $\mu : (\mathbb{A}_K)^{\times} \to \mathbb{C}^{\times}$ be a monoid homomorphism from the units of the adele ring of $\mathcal{O}_K$ in $K$ to $\mathbb{C}^{\times}$, assumed continuous. For a finite place $v$, i.e. a point of the height one spectrum of $\mathcal{O}_K$, the integer `pinnedExp K μ v` is the sum of two contributions: first, the natural number `conductorExponentAt K v (localChar μ v)`, cast to $\mathbb{Z}$, where `localChar μ v` is the character of $(K_v)^{\times}$ obtained by restricting $\mu$ along the map of unit groups induced by the embedding of the local units at $v$ into the finite adeles and then into the full adele ring, and where `conductorExponentAt` is the infimum of the set of $c$ satisfying the predicate `HasConductorExponentAt K v` for that character; second, `addCharLevel (psiLocal K v)`, the supremum of the set of integers $n$ such that the additive character $\psi_v$ kills every $x \in K_v$ with $\mathrm{v}(x) \le \exp(n)$, where $\psi_v$ = `psiLocal K v` is the standard additive character of the adeles of $K$ precomposed with the additive embedding of $K_v$ at the place $v$. The assertion is that the set of finite places $v$ with `pinnedExp K μ v ≠ 0` is finite.
--
--   This is the finiteness statement underlying the global factorisation of local constants in Tate's theory: a continuous idele class character is unramified outside a finite set, and the levels of the chosen local additive characters are governed by the different, so the local data of $\mu$ are normalised ('pinned') at all but finitely many places. It is used in the construction of global root numbers and conductors for Hecke characters, feeding into the comparison of a Hecke root number with the pinned root number and of the Hecke conductor with the induced conductor in rank two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_finite_setOf_pinnedExp_ne_zero_of_continuous.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem LanglandsTunnell.Converse.finite_setOf_pinnedExp_ne_zero_of_continuous
    (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : Continuous μ) :
    {v : HeightOneSpectrum (𝓞 K) | pinnedExp K μ v ≠ 0}.Finite := by sorry
