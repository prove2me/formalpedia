-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isModel_of_divisorLawFst_of_cuspLawInfty
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.isModel_of_divisorLawFst_of_cuspLawInfty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/132e8103-5830-5e05-aeae-faa154a10fd1
-- title:
--   Atkin–Lehner symmetry: two laws suffice for a model
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N \ge 1$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix further a modular polynomial datum `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$), a proof `hKr` that its bivariate reduction mod $q$ equals $(C(X)^q - X)\,(C(X) - X^q)$, and proofs `hα`, `hβ` that the two Hecke ring homomorphisms $\overline{\alpha}$, $\overline{\beta}$ at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a place specialisation of this data and $R :$ `ProlongationTuple P` a prolongation tuple over it, consisting of a residue-field map $\overline{red}$, an embedding $\iota$ of characteristic-$q$ function fields, two regular prolongations $R_1, R_2$ of $A$ to the level-$Nq$ function field $\overline{\mathbb{Q}}$-field, and the compatibilities relating $R_2$ to $R_1$ through the partial Atkin–Lehner map `atkinLehnerBar N q`. Assume $q \nmid N$, that $R$ satisfies `DivisorLawFst` — for every $f$ in the level-$Nq$ modular function field over $\overline{\mathbb{Q}}$ lying in the integers of both $R_1$ and $R_2$ with both residues nonzero, every divisor $D$ with $D(W) = \mathrm{ord}_W(f)$ at all places $W$, and every place $v$ of the characteristic-$q$ field with $\mathrm{Frob}^2(v) \ne v$, the pushforward along `P.reduceFst` of $D$ restricted to the places satisfying `P.IsStrictFst`, evaluated at $v$, equals $\mathrm{ord}_v$ of the first residue $R.\mathrm{residue}_1(f)$ — and that $R$ satisfies `CuspLawInfty` — the same hypotheses on $f$ and $D$, with the conclusion that for every place $c$ satisfying `IsInftySide P`, the pushforward along `P.reduceFst` of $D$ restricted to the $\infty$-side places, evaluated at `P.reduceFst c`, equals the order at `P.reduceFst c` of $R.\mathrm{residue}_1(f)$. Then $R$ is a model, i.e. all four laws `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty`, `CuspLawZero` hold.
--
--   This is the symmetry step in the study of the special fibre at $q$ of the level-$Nq$ modular curve: because the partial Atkin–Lehner involution interchanges the two reductions of places, the two notions of strict place and the two families of cusp branches, only one of each pair of laws has to be verified. It is used by [`ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed`](thm.html#ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed), where a prolongation tuple that is a model and satisfies the order law is produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isModel_of_divisorLawFst_of_cuspLawInfty.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.isModel_of_divisorLawFst_of_cuspLawInfty
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data} {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (hqN : ¬ q ∣ N) (h₁ : R.DivisorLawFst) (h₃ : R.CuspLawInfty) :
    R.IsModel := by sorry
