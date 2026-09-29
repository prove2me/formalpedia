-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawZero_oneSided
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.cuspLawZero_oneSided
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/a4d46eb2-0dc6-5746-81df-0acd7148edc1
-- title:
--   One-sided cusp law at the zero cusp
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ with $\Phi(j,j_q)=0$) together with a proof `hKr` that its reduction modulo $q$ is $(X^q-Y)(X-Y^q)$ in the bivariate sense of `KroneckerCongruence`, and hypotheses `hα`, `hβ` that the two degeneracy maps `heckeAlphaBar`, `heckeBetaBar` from level $1$ to level $q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place specialisation of the modular function field of level $1\cdot q$ over $A$ with residue data $(k,\mathrm{red})$, and let $R$ be a level-one prolongation pair for $P$: a lift $\overline{\mathrm{red}}$ of $\mathrm{red}$ to the residue field of $A$, an induced map $\iota$ on level-one function fields, and two regular prolongations $R_1, R_2$ of $A$ to `modularFunctionFieldBar (1 * q)` with values in the level-one function field over the residue field of $A$, linked by the Fricke involution ($f$ is $R_2$-integral exactly when its Fricke image is $R_1$-integral, and the $R_2$-residue of $f$ is the $R_1$-residue of its Fricke image). Let $f$ be an element of `modularFunctionFieldBar (1 * q)` lying in the integers of $R_2$ and with nonzero $R_2$-residue (no condition is imposed at $R_1$), and let $D$ be a finitely supported divisor on the places of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$ whose value at every place $W$ is $\operatorname{ord}_W(f)$. Restrict $D$ to the places satisfying `P.IsZeroSide`, i.e. those $W$ that are cuspidal for $P$ in the sense of `IsCuspidal'` and at which the chart `tZero` takes a value $\tau \in A$ with $\mathrm{red}\,\tau = 1$, and push the resulting divisor forward along $\mathrm{red}_2 : W \mapsto P.\mathrm{sp}(W|_{\mathrm{heckeBetaBar}})$. The theorem asserts that the coefficient of this pushforward at the place $\mathrm{red}_2(\bar 0)$, where $\bar 0$ is the Fricke translate `cuspZeroBar (1 * q)` of the cusp at infinity, equals the order at $\mathrm{red}_2(\bar 0)$ of the second residue `R.residue₂ ⟨f, h₂⟩` of $f$ in the level-one function field over $k$.
--
--   This is the cusp law on the zero side of the mod-$q$ fibre of $X_0(q)$: the fibre sum of $\operatorname{div} f$ over the residue disc of the cusp $\bar 0$ computes the order of the second residue of $f$ at the corresponding cusp of the $\tilde\jmath$-line, for zeros and poles alike and with no hypothesis at the first prolongation. It is the Fricke transport of `cuspLawInfty_oneSided`, and is used in the verification of the chart laws and in the construction of splitting data for level-one prolongation tuples.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawZero_oneSided.lean

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

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.cuspLawZero_oneSided
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (f : ↥(modularFunctionFieldBar (1 * q))) (h₂ : f ∈ R.R₂.integers) (hf : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f) :
    Finsupp.mapDomain P.redSnd (D.filter P.IsZeroSide) (P.redSnd (cuspZeroBar (1 * q))) =
      (P.redSnd (cuspZeroBar (1 * q))).ord (R.residue₂ ⟨f, h₂⟩) := by sorry
