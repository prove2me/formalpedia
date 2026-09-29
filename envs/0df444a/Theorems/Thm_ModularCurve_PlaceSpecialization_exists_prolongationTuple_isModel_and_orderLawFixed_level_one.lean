-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_and_orderLawFixed_level_one
-- name    : ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed_level_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/38c798de-ea73-5d5c-a671-0e235b712006
-- title:
--   A lawful prolongation tuple over a level-one place specialisation
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of an algebraic closure $\overline{\mathbf Q}$ of $\mathbf Q$, $k$ an algebraically closed field of characteristic $q$, and $\mathrm{red} : A \to k$ a surjective ring homomorphism. Fix modular-polynomial data at $q$, that is a monic $\Phi \in \mathbf Z[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions $(j, j_q)$, subject to the Kronecker congruence `hKr` that the bivariate reduction of $\Phi$ modulo $q$ equals $(X^{q} - Y)(X - Y^{q})$, and assume the hypotheses `hα`, `hβ` that the two degeneracy ring homomorphisms `heckeAlphaBar` and `heckeBetaBar` for level $1$ and prime $q$ over $\overline{\mathbf Q}$ are integral. Let $W$ be a finite set of places of the level-one function field `modularFunctionFieldC k 1`, the subfield of $k((q))$ generated over $k$ by the reduced $q$-expansions `jqModC` and `jqNModC` at $N = 1$, whose members are exactly the supersingular places `ssPlaces q 1 k`. The assertion is that there exist a place specialisation $P_1 \in$ `PlaceSpecialization A q 1 data hKr k red hα hβ` — a map $\mathrm{sp}$ from places of `modularFunctionFieldBar 1` over $\overline{\mathbf Q}$ to places of `modularFunctionFieldC k 1` together with a homomorphism on $\mathrm{Pic}^0$ and the listed compatibilities of orders of $j$ and $j_N$ with $\mathrm{red}$ — and a prolongation tuple $R$ over $P_1$ (a reduction $\overline{\mathrm{red}}$ on the residue field of $A$, an embedding $\iota$ acting coefficientwise by $\overline{\mathrm{red}}$, and two regular prolongations $R_1$, $R_2$ of `modularFunctionFieldBar (1 * q)` whose rings of integers are cut out by `modularLocalized` and by its pull-back along the Atkin–Lehner involution) such that: $R$ is a model, i.e. it satisfies both divisor laws and the cusp laws at $\infty$ and at $0$; $R$ satisfies the regularity law at $W$, so that for $f$ integral for both prolongations with no pole above an affine place $v$ fixed by the square of the geometric Frobenius the first residue is regular at $v$ and the second at the Frobenius translate of $v$, and residues take values at each node pair of $W$; $R$ satisfies the node-value law at $W$, so that nonzero residues of such an $f$ take a common nonzero value at the two places of any node pair not met by the divisor of $f$; and $R$ satisfies the fixed-place order law, so that for $f$ with both residues nonzero and $D$ the divisor of $f$, at every affine place $v$ fixed by the square of the geometric Frobenius the push-forward $(\mathrm{reduceFst})_*D$ at $v$ equals $\mathrm{ord}_v$ of the first residue plus $\mathrm{ord}$ at the Frobenius translate of $v$ of the second residue.
--
--   This is the level-one instance of the existence of a place specialisation of the modular curve carrying a prolongation tuple subject to all four laws; at level one the genus hypothesis present in the general statement is vacuous, and the regularity and node-value laws at the supersingular places are part of the conclusion. It underlies the unconditional existence statement [`ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed`](thm.html#ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed) and is used in the arguments on inertia-invariant points and on extending component homomorphisms, which encode the Deligne–Rapoport description of the reduction of $X_0(q)$ as two copies of the $j$-line crossing at the supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_and_orderLawFixed_level_one.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed_level_one
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q} [IsAlgClosed k]
    [DecidableEq k]
    (hred : Function.Surjective red)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) :
    ∃ P₁ : PlaceSpecialization A q 1 data hKr k red hα hβ,
      ∃ R : ProlongationTuple P₁, R.IsModel ∧ R.RegularityLaw W ∧ R.NodeValueLaw W ∧ R.OrderLawFixed := by sorry
