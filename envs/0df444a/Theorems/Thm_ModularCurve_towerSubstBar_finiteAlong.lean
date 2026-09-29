-- Prove2me | Theorems.Thm_ModularCurve_towerSubstBar_finiteAlong
-- name    : ModularCurve.towerSubstBar_finiteAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/93500f67-f5e0-5a05-8420-d46973e0ea40
-- title:
--   Finiteness of the degeneracy map q↦ q^ℓ to level M
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $N$ and $M$ be nonzero natural numbers, let $\ell$ be a prime, and assume $N\ell \mid M$. Write $F_n =$ `modularFunctionFieldFull n` for the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the family `divisorExpansions n`, and $L\cdot F_n =$ `laurentBaseChange L F_n` for the intermediate field of $L((q))$ generated over $L$ by the image of $F_n$ under the coefficient embedding $\mathbb{Q}((q)) \to L((q))$. The map `towerSubstBar L N ℓ h` is the $L$-algebra homomorphism $L\cdot F_N \to L\cdot F_M$ obtained by composing `heckeBetaBar L N ℓ`, the substitution $q \mapsto q^{\ell}$ from $L\cdot F_N$ into $L\cdot F_{N\ell}$, with the inclusion `towerInclBar` of $L\cdot F_{N\ell}$ into $L\cdot F_M$ coming from $N\ell \mid M$. The assertion is `FiniteAlong L` of this map: with $L\cdot F_M$ regarded as an algebra over $L\cdot F_N$ via `towerSubstBar L N ℓ h`, it is a finite module over $L\cdot F_N$.
--
--   On function fields this is the finiteness of the degeneracy map $\tau \mapsto \ell\tau$ from level $N$ to any level divisible by $N\ell$, expressed as module-finiteness of the corresponding field extension. It supplies the finiteness hypothesis in the Hecke correspondence formalism, and is used in the Hecke exchange and diagonal identities at primes and in the computation of the cuspidal divisor of the Hecke divisor map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_towerSubstBar_finiteAlong.lean

import Definitions.Def_ModularCurve_DegeneracyTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.towerSubstBar_finiteAlong (L : Type*) [Field L] [Algebra ℚ L] {N M : ℕ} [NeZero N] [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] (h : N * ℓ ∣ M) : FiniteAlong L (towerSubstBar L N ℓ h) := by sorry
