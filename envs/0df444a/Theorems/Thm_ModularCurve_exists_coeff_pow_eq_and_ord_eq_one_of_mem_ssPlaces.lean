-- Prove2me | Theorems.Thm_ModularCurve_exists_coeff_pow_eq_and_ord_eq_one_of_mem_ssPlaces
-- name    : ModularCurve.exists_coeff_pow_eq_and_ord_eq_one_of_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/3d92c17a-01a6-5054-b515-a10b58c4dc48
-- title:
--   Frobenius-fixed affine uniformiser at a supersingular place
-- statement:
--   Let $q$ be a prime, $N$ a nonzero natural number with $q \nmid N$, and $k$ an algebraically closed field of characteristic $q$. Write $F = \mathrm{modularFunctionFieldC}\,k\,N$ for the intermediate field of the Laurent series field $k((\mathsf q))$ generated over $k$ by the two series `jqModC k` and `jqNModC k N`. A place of $F$ over $k$ is, in this project, a valuation subring of $F$ containing the image of $k$, different from $F$, and a principal ideal ring; `ord` denotes the associated $\mathbb Z$-valued order, minus the logarithm of the adic valuation. Let $w$ be such a place lying in `ssPlaces q N k`, that is: $w$ is rational, both generators `jGeomGen k N` and `jNGeomGen k N` lie in the valuation subring of $w$ (the predicate `IsAffineGeomPlace`), and the value of `jGeomGen k N` at $w$ lies in `ssJSet q k`. The assertion is that there exists $t \in F$ such that (i) every Laurent coefficient $c_n$ of $t$ satisfies $c_n^q = c_n$, so all coefficients lie in the prime field; (ii) $t$ lies in the valuation subring of every place $u$ of $F$ over $k$ satisfying `IsAffineGeomPlace k N u`; and (iii) $w.\mathrm{ord}\,t = 1$ and also $(\varphi \cdot w).\mathrm{ord}\,t = 1$, where $\varphi =$ `arithFrobC q k N` is the semilinear automorphism of $F$ over $k$ obtained by applying the $q$-power Frobenius of $k$ to the Laurent coefficients, acting on places by the pointwise action.
--
--   This provides the uniformiser used in the Frobenius-order computation on the supersingular locus of the level-$N$ modular curve in characteristic $q$: a function with coefficients in $\mathbb F_q$, regular on the affine part, with simple zeros at a supersingular place and at its arithmetic Frobenius translate. It is the input to [`ModularCurve.exists_coeff_pow_eq_and_ord_sub_pow_sq_eq_one_of_mem_ssPlaces`](thm.html#ModularCurve.exists_coeff_pow_eq_and_ord_sub_pow_sq_eq_one_of_mem_ssPlaces), where the factorisation of $t - t^{q^2}$ turns these two simple zeros into an order statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_coeff_pow_eq_and_ord_eq_one_of_mem_ssPlaces.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

theorem ModularCurve.exists_coeff_pow_eq_and_ord_eq_one_of_mem_ssPlaces
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (hqN : ¬ q ∣ N) (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) :
    ∃ t : ↥(modularFunctionFieldC k N),
      (∀ n : ℤ, ((t : LaurentSeries k).coeff n) ^ q = (t : LaurentSeries k).coeff n) ∧
      (∀ u : Place k (modularFunctionFieldC k N), IsAffineGeomPlace k N u → t ∈ u.toValuationSubring) ∧
      w.ord t = 1 ∧ (arithFrobC q k N • w).ord t = 1 := by sorry
