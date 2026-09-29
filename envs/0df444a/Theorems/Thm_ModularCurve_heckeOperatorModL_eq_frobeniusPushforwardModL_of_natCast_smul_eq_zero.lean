-- Prove2me | Theorems.Thm_ModularCurve_heckeOperatorModL_eq_frobeniusPushforwardModL_of_natCast_smul_eq_zero
-- name    : ModularCurve.heckeOperatorModL_eq_frobeniusPushforwardModL_of_natCast_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/1d48e813-79fc-5260-9e7f-7d083d2ea49d
-- title:
--   On ℓ-torsion, ̄ T_ℓ equals the Frobenius push-forward
-- statement:
--   Let $K$ be an algebraically closed field, $\ell$ a prime with $\operatorname{char} K = \ell$, and $N$ a nonzero natural number. Write $F =$ `modularFunctionFieldFullC K N` for the intermediate field of the Laurent series field $K((q))$ obtained by adjoining to $K$ the family `divisorExpansionsC K N`, and let `JZeroC K N` be $\operatorname{Pic}^0$ of this function field, i.e. the group of degree-zero divisors modulo the subgroup of principal divisors contained in it. The assertion is: for every $x$ in `JZeroC K N` satisfying $(\ell : \mathbb{Z}) \cdot x = 0$, one has $$\bigl(\mathrm{Fr}_* + \mathrm{Fr}^*\bigr)(x) = \mathrm{Fr}_*(x),$$ where `heckeOperatorModL K N ℓ` is by definition the sum of the two endomorphisms `frobeniusPushforwardModL K N ℓ` and `frobeniusPullbackModL K N ℓ` of `JZeroC K N`. Each of the latter two is defined by cases on the predicate `FrobeniusInputsModL K N ℓ`, which packages the existence of principal divisors for $F$, finiteness of the map `frobeniusModL K N ℓ` along places, and the fundamental identity and norm formula for that map: when these hold, the maps are the descents to $\operatorname{Pic}^0$ of push-forward and pull-back of divisors along `frobeniusModL K N ℓ`, and otherwise both are the zero homomorphism. Equivalently, the statement says that $\mathrm{Fr}^*$ annihilates $x$.
--
--   This is the mod-$\ell$ form of the Eichler–Shimura congruence relation on $\ell$-torsion: in characteristic $\ell$ the Hecke operator $\bar T_\ell = \mathrm{Fr}_* + \mathrm{Fr}^*$ on $J_0(N)$ reduces, on points killed by $\ell$, to the Frobenius push-forward alone, because $\mathrm{Fr}^*$ factors through multiplication by $\ell$. It is used in the analysis of the ordinary filtration and of Hecke torsion in the special fibre, in particular by [`ModularCurve.exists_ordinaryFiltration_heckeTorsion_jZero_of_heckeGen_notMem_of_ne_two`](thm.html#ModularCurve.exists_ordinaryFiltration_heckeTorsion_jZero_of_heckeGen_notMem_of_ne_two) and [`ModularCurve.pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL`](thm.html#ModularCurve.pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeOperatorModL_eq_frobeniusPushforwardModL_of_natCast_smul_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperatorModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem ModularCurve.heckeOperatorModL_eq_frobeniusPushforwardModL_of_natCast_smul_eq_zero
    (K : Type*) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    (x : JZeroC K N) (hx : (ℓ : ℤ) • x = 0) :
    heckeOperatorModL K N ℓ x = frobeniusPushforwardModL K N ℓ x := by sorry
