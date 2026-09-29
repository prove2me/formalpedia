-- Prove2me | Theorems.Thm_ModularCurve_frobeniusPullbackModL_frobeniusPushforwardModL
-- name    : ModularCurve.frobeniusPullbackModL_frobeniusPushforwardModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/ace4f4e5-719c-57cf-b253-49f9c37fa887
-- title:
--   Frobenius pullback after pushforward on J₀(N) equals ℓ
-- statement:
--   Let $K$ be an algebraically closed field, $\ell$ a prime, and suppose $K$ has characteristic $\ell$; let $N \ge 1$ be an integer with $\ell \nmid N$. Write $J_0(N)$ for [`ModularCurve.JZeroC K N`](def/ModularCurve_X0ModL.html#L148), the divisor class group `Pic0` of the intermediate field $\mathrm{modularFunctionFieldFullC}\,K\,N \subseteq K((q))$ obtained by adjoining to $K$ the expansions `divisorExpansionsC K N`, that is, the group of degree-zero divisors of that field modulo the subgroup of principal divisors. The two endomorphisms in play are [`ModularCurve.frobeniusPushforwardModL K N ℓ`](def/ModularCurve_FrobeniusModL.html#L281) and [`ModularCurve.frobeniusPullbackModL K N ℓ`](def/ModularCurve_FrobeniusModL.html#L288): each is defined by cases on the predicate `FrobeniusInputsModL K N ℓ`, which asserts that principal divisors are available for this function field, that the map `frobeniusModL K N ℓ` is finite along, and that the fundamental identity and the norm formula hold along it; when that package holds they are the additive endomorphisms of $J_0(N)$ induced by the degree-zero pushforward, respectively pullback, along `frobeniusModL K N ℓ`, and otherwise both are the zero map. The assertion is that for every $y \in J_0(N)$ one has $\mathrm{Fr}^{*}(\mathrm{Fr}_{*}\,y) = \ell \cdot y$.
--
--   This is the statement that pullback composed with pushforward along the characteristic-$\ell$ Frobenius on $\mathrm{Pic}^0$ of the modular function field is multiplication by $\ell$, the Frobenius–Verschiebung relation on the Jacobian, stated without hypotheses beyond $K$ algebraically closed of characteristic $\ell$ and $\ell \nmid N$. It is used together with its companion in the other order, and in the comparison of Hecke and degeneracy maps on the Néron model data at $\ell$ that feeds the mod-$\ell$ analysis of $J_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frobeniusPullbackModL_frobeniusPushforwardModL.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperatorModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.frobeniusPullbackModL_frobeniusPushforwardModL
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (N : ℕ) [NeZero N] (hℓN : ¬ ℓ ∣ N) (y : ModularCurve.JZeroC K N) :
    ModularCurve.frobeniusPullbackModL K N ℓ (ModularCurve.frobeniusPushforwardModL K N ℓ y) = ℓ • y := by sorry
