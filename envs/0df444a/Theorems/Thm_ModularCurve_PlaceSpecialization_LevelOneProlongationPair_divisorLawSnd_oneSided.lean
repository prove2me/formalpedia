-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawSnd_oneSided
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.divisorLawSnd_oneSided
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/afd4bd47-eb03-5210-a6cb-6f4d61bc4a73
-- title:
--   One-sided divisor law for the second level-one prolongation
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix data `data : ModularPolynomialData q`, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ with $\Phi(j, j_q) = 0$, together with the Kronecker congruence `hKr` asserting that the reduction of $\Phi$ modulo $q$ equals $(C(X)^{q}-X)(C(X)-X^{q})$, and the hypotheses $h\alpha$, $h\beta$ that the two Hecke maps `heckeAlphaBar`, `heckeBetaBar` at level $1$ and prime $q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place specialisation for these data and $R$ a level-one prolongation pair for $P$, so in particular $R$ carries two regular prolongations $R_1, R_2$ of $A$ in the field `modularFunctionFieldBar (1 * q)` with values in the level-one function field over the residue field of $A$, interchanged by the Fricke involution. Let $f$ be an element of `modularFunctionFieldBar (1 * q)` lying in the integers of $R_2$ and whose $R_2$-residue is nonzero, and let $D$ be a divisor, i.e. a finitely supported integer-valued function on the places of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$ (a place being a proper valuation subring containing $\overline{\mathbb Q}$ whose ring is a principal ideal ring), such that $D(W) = \operatorname{ord}_W f$ for every place $W$. Let $v$ be a place of `modularFunctionFieldC k 1` over $k$ with $\varphi(\varphi(v)) \neq v$, where $\varphi$ is `frobOnPlacesGeomLevel`. Then the value at $v$ of the pushforward along `P.redSnd` of the restriction of $D$ to the places of strict type two equals $\operatorname{ord}_v$ of `R.residue₂ ⟨f, h₂⟩`, the element of `modularFunctionFieldC k 1` attached to the $R_2$-residue of $f$. Here `P.redSnd W` is the specialisation `P.sp` applied to the restriction of $W$ along `heckeBetaBar`, and $W$ has strict type two when $P.\mathrm{redFst}(W) = \varphi(P.\mathrm{redSnd}(W))$ and $\varphi(\varphi(P.\mathrm{redSnd}(W))) \neq P.\mathrm{redSnd}(W)$; so the left-hand side is the finite sum of $\operatorname{ord}_W f$ over the strict-type-two places $W$ with $P.\mathrm{redSnd}(W) = v$.
--
--   This is the fibre-sum (divisor) law on the second of the two branches of the special fibre of $X_0(q)$ in characteristic $q$, in a one-sided form: only integrality and nonvanishing of the residue at the second prolongation are assumed, and the divisor may be prescribed arbitrarily subject to computing the orders of $f$. It is used in the level-one prolongation-tuple layer, where it feeds the cusp laws at $0$ and at $\infty$ and the corresponding first-branch statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawSnd_oneSided.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve
open Classical in

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.divisorLawSnd_oneSided
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (f : ↥(modularFunctionFieldBar (1 * q))) (h₂ : f ∈ R.R₂.integers) (hf : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f)
    (v : Place k ↥(modularFunctionFieldC k 1))
    (hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v) :
    Finsupp.mapDomain P.redSnd (D.filter P.IsStrictTypeTwo) v = v.ord (R.residue₂ ⟨f, h₂⟩) := by sorry
