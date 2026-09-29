-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_isAlgClosed
-- name    : ModularCurve.PlaceSpecialization.isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/813364d9-d5b6-5222-a7e5-e218faed142a
-- title:
--   A level-one place specialisation forces k algebraically closed
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, a field $k$ of characteristic $q$, and a ring homomorphism $\mathrm{red} \colon A \to k$. Fix further `data : ModularPolynomialData q`, that is a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ in $Y$ annihilating the pair $(j(q_{\mathrm{var}}), j)$ in the sense of `eval_eq_zero`, together with a proof `hKr` of the Kronecker congruence that the reduction of $\Phi$ modulo $q$ equals $(C(X)^{q} - X)\,(C(X) - X^{q})$ in $(\mathbb{Z}/q)[X][Y]$, and proofs `hα`, `hβ` that the two level-raising maps `heckeAlphaBar` and `heckeBetaBar` from the base-changed modular function field of level $1$ to that of level $1\cdot q$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Assume given a term $P$ of the structure `PlaceSpecialization A q 1 data hKr k red hα hβ`: a map $\mathrm{sp}$ from the places of the level-one modular function field over $\overline{\mathbb{Q}}$ to the places of `modularFunctionFieldC k 1` (the subfield of $k((q))$ generated over $k$ by `jqModC k` and `jqNModC k 1`), a homomorphism on degree-zero divisor classes, and the compatibility clauses of that structure, among them the requirement that $\mathrm{sp}$ hit every place. The conclusion is that $k$ is algebraically closed.
--
--   This is a genericity constraint on the target field of a place specialisation of the level-one modular curve: the existence of such a specialisation packet over $k$ already forces $k$ to be algebraically closed. It is used by the prolongation-pair lemmas built on top of the place-specialisation packet, which may therefore argue over an algebraically closed residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.isAlgClosed
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) : IsAlgClosed k := by sorry
