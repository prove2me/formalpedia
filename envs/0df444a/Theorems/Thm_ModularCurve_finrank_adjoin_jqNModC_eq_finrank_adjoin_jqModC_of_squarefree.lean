-- Prove2me | Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_eq_finrank_adjoin_jqModC_of_squarefree
-- name    : ModularCurve.finrank_adjoin_jqNModC_eq_finrank_adjoin_jqModC_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/1345e1e0-2c6a-5f83-9c58-339ca1045e3a
-- title:
--   Equal degrees of K over L(j(q)) and L(j(q^N))
-- statement:
--   Let $L$ be a field of characteristic zero and let $N$ be a nonzero natural number which is squarefree and satisfies $N > 1$. Inside the Laurent series field $L((q))$ over $L$, write $j(q)$ for [`ModularCurve.jqModC L`](def/ModularCurve_JqCoeff.html#L15), the Laurent series $q^{-1}$ times the image in $L[[q]]$ of the integral power series `jNum` $= E_4^3 \cdot$ `dedekindEtaUnitInv`, and $j(q^N)$ for [`ModularCurve.jqNModC L N`](def/ModularCurve_JqCoeff.html#L18), the image of $j(q)$ under the ring homomorphism `qExpand L N` of $L((q))$ that multiplies all exponents by $N$ (substitution $q \mapsto q^N$). Let $K$ be an intermediate field of $L((q))$ over $L$, and let $x, y \in K$ be elements whose images in $L((q))$ are $j(q)$ and $j(q^N)$ respectively. Assume that $K$ is finite-dimensional over the simple intermediate field $L(x) \subseteq K$. Then $K$ has the same (finite) rank over $L(y)$ as over $L(x)$, both ranks being taken as `Module.finrank` of $K$ over the intermediate fields of $K$ generated over $L$ by the single elements $y$ and $x$.
--
--   This is the statement that changing the base of a modular function field from the $j$-line to the line of $j(q^N)$ leaves degrees unchanged, the function-field form of the symmetry of the classical modular polynomial $\Phi_N(X,Y)$ for $N>1$. It is used in the treatment of modular curves at full level, in the computation of ranks of function fields of level-$H$ models and in a rank computation over a fraction ring arising in the classification of rigid data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_adjoin_jqNModC_eq_finrank_adjoin_jqModC_of_squarefree.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.finrank_adjoin_jqNModC_eq_finrank_adjoin_jqModC_of_squarefree
    (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N] (hN : Squarefree N) (hN1 : 1 < N)
    (K : IntermediateField L (LaurentSeries L)) (x y : ↥K)
    (hx : (x : LaurentSeries L) = ModularCurve.jqModC L)
    (hy : (y : LaurentSeries L) = ModularCurve.jqNModC L N)
    [FiniteDimensional ↥(IntermediateField.adjoin L ({x} : Set ↥K)) ↥K] :
    Module.finrank ↥(IntermediateField.adjoin L ({y} : Set ↥K)) ↥K =
      Module.finrank ↥(IntermediateField.adjoin L ({x} : Set ↥K)) ↥K := by sorry
