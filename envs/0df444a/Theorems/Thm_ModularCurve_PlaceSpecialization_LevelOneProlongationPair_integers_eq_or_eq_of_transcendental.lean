-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_integers_eq_or_eq_of_transcendental
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.integers_eq_or_eq_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/cea15323-818e-5647-a07e-c83c4b3359cb
-- title:
--   Only two prolongations with transcendental j-residue
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $q$ in the sense that $q$ is a nonunit of $A$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Fix further modular polynomial data for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ with $\Phi(j, j_q) = 0$) satisfying the Kronecker congruence $\Phi \bmod q = (X^q - Y)(X - Y^q)$, integrality hypotheses $h\alpha$, $h\beta$ for the two Hecke maps $\overline{\alpha}$, $\overline{\beta}$ at level $1$ and prime $q$, a place specialisation $P$ for these data at level $N = 1$, and a level-one prolongation pair $V$ for $P$, which in particular provides two regular prolongations $V.R_1$, $V.R_2$ of $A$ to the field $\overline{\mathbb Q}$-base-changed full modular function field of level $1\cdot q$, both with residue field the full modular function field of level $1$ over the residue field of $A$. Let $\bar F$ be a field extension of the residue field of $A$ and let $R$ be a regular prolongation of $A$ to the same level-$(1\cdot q)$ function field with residue field $\bar F$: a valuation subring $R.\mathrm{integers}$ together with a surjective homomorphism onto $\bar F$ whose kernel is the maximal ideal, whose intersection with $\overline{\mathbb Q}$ is exactly $A$, which is compatible with reduction on $A$, and for which every nonzero element of the function field has a scalar multiple that is integral with nonzero residue. Assume the element `jFun`, the image of the $q$-expansion of $j$ in that function field, lies in $R.\mathrm{integers}$ and that its residue is transcendental over the residue field of $A$. Then $R.\mathrm{integers}$ equals $V.R_1.\mathrm{integers}$ or $V.R_2.\mathrm{integers}$.
--
--   This is the uniqueness half of the Hensel-type splitting of the Gauss valuation of $\overline{\mathbb Q}(j)$ in the modular function field of level $q$: the two prolongations supplied by a level-one prolongation pair, corresponding to the two coprime factors of $\Phi$ modulo $q$, are the only ones with transcendental residue of $j$, by the fundamental inequality $\sum_i [\bar F_i : k_0(\mathrm{res}_i j)] \le [F : \overline{\mathbb Q}(j)] = q+1$ applied to $\{V.R_1, V.R_2, R\}$. It is used to recognise a given prolongation as one of the two, in the place-language form of the statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_integers_eq_or_eq_of_transcendental.lean

import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.integers_eq_or_eq_of_transcendental
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (V : P.LevelOneProlongationPair)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A (modularFunctionFieldBar (1 * q)) Fbar)
    (hj : PlaceSpecialization.jFun (q := q) ∈ R.integers)
    (htr : Transcendental (ResidueField A) (R.residue ⟨_, hj⟩)) :
    R.integers = V.R₁.integers ∨ R.integers = V.R₂.integers := by sorry
