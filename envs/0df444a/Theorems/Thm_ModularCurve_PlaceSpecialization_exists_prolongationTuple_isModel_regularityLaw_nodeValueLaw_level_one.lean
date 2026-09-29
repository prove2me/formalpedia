-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw_level_one
-- name    : ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw_level_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/6f45b089-d644-5266-bb7a-1597c610a202
-- title:
--   Existence of a lawful level-one prolongation tuple
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbf{Q}}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, and modular polynomial data at $q$, i.e. a monic $\Phi \in (\mathbf{Z}[X])[Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions, subject to the Kronecker congruence that $\Phi$ reduced modulo $q$ equals $(C(X)^{q} - X)\,(C(X) - X^{q})$, together with hypotheses $h\alpha$, $h\beta$ asserting that the two level-$q$ degeneracy maps `heckeAlphaBar` and `heckeBetaBar` over $\overline{\mathbf{Q}}$ at level $1$ are integral ring homomorphisms. Let $P$ be a place specialisation `PlaceSpecialization A q 1 data hKr k red hα hβ`, and let $W$ be a finite set of places of the level-one function field $\mathrm{modularFunctionFieldC}\,k\,1$ over $k$ whose members are exactly the supersingular places `ssPlaces q 1 k`. Then there exists a prolongation tuple $R$ over $P$ — a reduction $\overline{\mathrm{red}}$ of the residue field of $A$ to $k$ lifting $\mathrm{red}$, a coefficientwise-compatible embedding of the level-one function field over the residue field of $A$ into $\mathrm{modularFunctionFieldC}\,k\,1$, and two regular prolongations $R_1$, $R_2$ of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ whose integer rings are cut out by membership in `CharPReduction.modularLocalized`, the second via the Atkin–Lehner involution, with matching residue maps — such that $R$ is a model (both divisor laws and both cusp laws at $\infty$ and $0$ hold), $R$ satisfies the regularity law at $W$ (for $f$ integral for both $R_1$ and $R_2$: nonnegativity of the orders of the two residues at an affine place $v$ fixed by the square of the geometric Frobenius and at its Frobenius image, whenever $f$ has nonnegative order at every place above $v$; and existence of a common value of the two residues at the two members of each node pair in `nodePairsOfPlaces (arithFrobC q k 1) W`), $R$ satisfies the node value law at $W$ (the common value at a node pair may be taken nonzero when both residues are nonzero and no zero or pole of $f$ reduces to that pair), and $R$ satisfies the fixed-place order law (for $f$ with both residues nonzero, the pushforward along $P.\mathrm{reduceFst}$ of the divisor of $f$ has multiplicity at such a $v$ equal to the order of the first residue at $v$ plus the order of the second residue at the Frobenius image of $v$).
--
--   This is the level-one instance of the construction, for a given place specialisation, of a prolongation tuple satisfying all the laws that encode the Deligne–Rapoport description of the reduction of $X_0(q)$ modulo $q$ as two copies of the level-one curve crossing transversally at the supersingular points. It is the input to the subsequent analysis of divisor classes, inertia action and one-sided regularity on that reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw_level_one.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw_level_one
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q} [IsAlgClosed k]
    [DecidableEq k]
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) :
    ∃ R : ProlongationTuple P, R.IsModel ∧ R.RegularityLaw W ∧ R.NodeValueLaw W ∧ R.OrderLawFixed := by sorry
