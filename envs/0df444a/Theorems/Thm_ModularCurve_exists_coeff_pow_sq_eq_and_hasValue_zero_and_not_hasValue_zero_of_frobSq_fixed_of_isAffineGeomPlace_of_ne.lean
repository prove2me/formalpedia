-- Prove2me | Theorems.Thm_ModularCurve_exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_frobSq_fixed_of_isAffineGeomPlace_of_ne
-- name    : ModularCurve.exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_frobSq_fixed_of_isAffineGeomPlace_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/f3076997-55eb-5220-a368-86304561d9ec
-- title:
--   Frobenius-fixed affine function separating a φ²-fixed place
-- statement:
--   Let $q$ be a prime, let $N$ be a positive integer with $q \nmid N$, and let $k$ be an algebraically closed field of characteristic $q$. Work in the function field $F =$ `modularFunctionFieldC k N`, the subfield of the Laurent series field $k((\mathsf q))$ generated over $k$ by `jqModC k` and its $N$-fold expansion `jqNModC k N`. A place of $F$ over $k$ is a valuation subring of $F$ that contains the image of $k$, is not all of $F$, and is a principal ideal ring. Let $w, w'$ be two such places, assume $w \ne w'$, assume that $w$ is fixed by the square of the semilinear automorphism `arithFrobC q k N` acting on places (the automorphism of $F$ raising each Laurent coefficient to the $q$-th power, paired with the Frobenius of $k$), and assume $w$ is affine in the sense that both `jGeomGen k N` and `jNGeomGen k N` — the elements $j$ and $j_N$ of $F$ — lie in the valuation subring of $w$. Then there exists $t \in F$ such that: every Laurent coefficient $c_n$ of $t$ satisfies $c_n^{q^2} = c_n$; $t$ lies in the valuation subring of every affine place $u$ (i.e. of every place containing $j$ and $j_N$); $t$ has value $0$ at $w$, meaning $t$ lies in the valuation subring of $w$ with residue $0$; and $t$ does not have value $0$ at $w'$, i.e. it is not the case that $t$ lies in the valuation subring of $w'$ with residue $0$.
--
--   This provides a regular function on the affine part of the special fibre of the level-$N$ modular curve in characteristic $q$ whose $\mathsf q$-expansion has all coefficients in $\mathbb{F}_{q^2}$, vanishing at a prescribed $\varphi^2$-fixed affine place and not vanishing at any other prescribed place (the condition at $w'$ is automatic where $t$ has a pole, so $w'$ may be a cusp). It is used to obtain the corresponding separation statement for supersingular places, [`ModularCurve.exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_mem_ssPlaces_of_ne`](thm.html#ModularCurve.exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_mem_ssPlaces_of_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_frobSq_fixed_of_isAffineGeomPlace_of_ne.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

theorem
ModularCurve.exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_frobSq_fixed_of_isAffineGeomPlace_of_ne
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k]
    (hqN : ¬ q ∣ N) (w w' : Place k (modularFunctionFieldC k N))
    (hfix : arithFrobC q k N • (arithFrobC q k N • w) = w) (haff : IsAffineGeomPlace k N w) (hne : w ≠ w') :
    ∃ t : ↥(modularFunctionFieldC k N),
      (∀ n : ℤ, ((t : LaurentSeries k).coeff n) ^ (q ^ 2) = (t : LaurentSeries k).coeff n) ∧
      (∀ u : Place k (modularFunctionFieldC k N), IsAffineGeomPlace k N u → t ∈ u.toValuationSubring) ∧
      w.HasValue t (0 : k) ∧ ¬ w'.HasValue t (0 : k) := by sorry
