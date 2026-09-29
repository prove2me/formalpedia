-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawInfty_oneSided
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.cuspLawInfty_oneSided
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/26709e93-0fe8-513d-8e3e-e8345c533cac
-- title:
--   One-sided cusp law at ∞ for the first prolongation
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix data $\Phi \in \mathbb Z[X][Y]$ for level $q$ (monic of degree $\psi(q)$ in $Y$ with $\Phi(j, j_q) = 0$) together with the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q) \pmod q$, and the integrality hypotheses $h\alpha$, $h\beta$ saying that the two Hecke maps $\bar\alpha$, $\bar\beta$ from level $1$ to level $q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place specialisation of level $1$ for these data, and let $R$ be a level-one prolongation pair for $P$: a homomorphism $\overline{\mathrm{red}}$ from the residue field of $A$ to $k$ lifting $\mathrm{red}$, an embedding $\iota$ of level-one function fields realised by coefficientwise application of $\overline{\mathrm{red}}$, and two regular prolongations $R_1, R_2$ of $\overline{\mathbb Q}$-valued level-$1\cdot q$ modular function field to the level-one function field over the residue field of $A$, with $R_1$ computing residues of Laurent series with coefficients in $A$ by coefficientwise reduction, $R_2$ obtained from $R_1$ by the Fricke involution (both on integers and on residues), and $\iota \circ R_1$-residue agreeing with the localised modular reduction homomorphism. Let $f$ be an element of the modular function field of level $1\cdot q$ over $\overline{\mathbb Q}$ lying in the integers of $R_1$ and with nonzero $R_1$-residue, and let $D$ be a divisor (a finitely supported $\mathbb Z$-valued function on the places of that field over $\overline{\mathbb Q}$) with $D(W) = \operatorname{ord}_W(f)$ for every place $W$. Restrict $D$ to the places $W$ satisfying $P$'s $\infty$-side condition, namely that $W$ is $P$-cuspidal and that $t_\infty$ has a $W$-value $\tau \in A$ with $\mathrm{red}(\tau) = 1$, and push this restriction forward along $P.\mathrm{redFst}$, the map sending a place to the $P$-specialisation of its restriction along $\bar\alpha$. The assertion is that the value of the resulting finitely supported function at $P.\mathrm{redFst}(\overline\infty)$, where $\overline\infty$ is the cusp $\infty$ at level $1\cdot q$, equals $\operatorname{ord}$ at $P.\mathrm{redFst}(\overline\infty)$ of the $R_1$-residue of $f$.
--
--   This is the cusp law at $\infty$ in one-sided form: the fibre sum of $\operatorname{ord}_W(f)$ over the $\infty$-side places of the cuspidal region lying above the reduced cusp records the order of the residue of $f$ on the first component, with no hypothesis imposed at the second prolongation and for zeros as well as poles. It is used by the chart laws for the first component of the reduction and, via Fricke transport, by the companion statement [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.cuspLawZero_oneSided`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.cuspLawZero_oneSided) on the $0$-side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawInfty_oneSided.lean

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

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.cuspLawInfty_oneSided
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (f : ↥(modularFunctionFieldBar (1 * q))) (h₁ : f ∈ R.R₁.integers) (hf : R.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f) :
    Finsupp.mapDomain P.redFst (D.filter P.IsInftySide) (P.redFst (cuspInftyBar (1 * q))) =
      (P.redFst (cuspInftyBar (1 * q))).ord (R.residue₁ ⟨f, h₁⟩) := by sorry
