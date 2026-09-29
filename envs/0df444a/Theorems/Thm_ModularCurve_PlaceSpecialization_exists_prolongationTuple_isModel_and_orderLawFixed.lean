-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_and_orderLawFixed
-- name    : ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/c698ff2b-5fe7-5a5c-912d-c99cddfa6940
-- title:
--   Existence of a place specialization carrying a model prolongation tuple
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$ (the `AlgebraicClosure` of $\mathbb{Q}$), $N$ a nonzero natural number, $k$ an algebraically closed field of characteristic $q$, and $red : A \to k$ a ring homomorphism. Let `data` be a `ModularPolynomialData q`, i.e. a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ with $\Phi(\mathrm{evalAtJ}, j_{q})=0$, and let `hKr` assert the Kronecker congruence $\Phi \bmod q = (C(X)^q - X)(C(X) - X^q)$; let `hα`, `hβ` assert that the ring homomorphisms `heckeAlphaBar` and `heckeBetaBar` at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral. Assume $q \nmid N$, that $red$ is surjective, and that $W$ is a finite set of places of `modularFunctionFieldC k N` whose members are exactly the places $w$ with `IsSupersingularPlace q N k w`. Then there exist a `PlaceSpecialization A q N data hKr k red hα hβ` $P_0$ — a map $sp$ from places of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ to places of `modularFunctionFieldC k N` together with a homomorphism from `JZero N` to $\mathrm{Pic}^0$ of `modularFunctionFieldC k N`, subject to the compatibilities of $sp$ with orders of $j$ and $j_N$ and their poles — and a `ProlongationTuple P₀` $R$, consisting of a lift $\overline{red}$ of $red$ through the residue field of $A$, a homomorphism $\iota$ of `modularFunctionFieldFullC (ResidueField A) N` into `modularFunctionFieldC k N` given coefficientwise by $\overline{red}$, and two regular prolongations $R_1, R_2$ of $A$ from `modularFunctionFieldBar (N*q)` to `modularFunctionFieldFullC (ResidueField A) N` whose rings of integers are, respectively, the localised modular ring `CharPReduction.modularLocalized (N*q) A red` and its pullback under the Atkin–Lehner involution, with the matching residue identities, such that: $R$ is a model, i.e. satisfies `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty` and `CuspLawZero`; $R$ satisfies the regularity law at $W$ (for $f$ integral for both prolongations: at any affine geometric place $v$ fixed by the square of `frobOnPlacesGeomLevel`, non-negativity of $\mathrm{ord}_V f$ at all $V$ with $\mathrm{reduceFst}\,V = v$ forces non-negative order of the nonzero first residue at $v$ and of the nonzero second residue at the Frobenius image of $v$, and at every node pair $s$ in `nodePairsOfPlaces (arithFrobC q k N) W` the two residues take a common value at $s_1$ and $s_2$); $R$ satisfies the node-value law at $W$ (if both residues are nonzero and no place $V$ with $\mathrm{ord}_V f \neq 0$ reduces to $(s_1,s_2)$, the common value at $s$ is nonzero); and $R$ satisfies the fixed-place order law, that for $f$ with both residues nonzero and $D$ the divisor of $f$, the pushforward of $D$ along $\mathrm{reduceFst}$ at an affine geometric place $v$ fixed by the square of `frobOnPlacesGeomLevel` equals $\mathrm{ord}_v$ of the first residue plus the order at the Frobenius image of $v$ of the second residue.
--
--   This is the existence statement for the supersingular-reduction model of $X_0(Nq)$ in the shape used here: a specialization of places from characteristic zero to characteristic $q$, together with the pair of Gauss prolongations recording the two degeneracy legs, subject to the divisor, cusp, regularity, node-value and fixed-place order laws. It is the input to the analysis of node residues and of admissible divisor classes, and to the variants of the same existence statement formulated for a given specialization or under a genus hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_and_orderLawFixed.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open Classical in

theorem ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    (hqN : ¬ q ∣ N)
    (hred : Function.Surjective red)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) :
    ∃ P₀ : PlaceSpecialization A q N data hKr k red hα hβ,
      ∃ R : ProlongationTuple P₀, R.IsModel ∧ R.RegularityLaw W ∧ R.NodeValueLaw W ∧ R.OrderLawFixed := by sorry
