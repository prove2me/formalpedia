-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_iff_and_isStrictSnd_iff_of_isModel_of_isModel
-- name    : ModularCurve.PlaceSpecialization.isStrictFst_iff_and_isStrictSnd_iff_of_isModel_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/be01312f-f995-5dfb-adb6-e55d2810b8bf
-- title:
--   Model prolongation tuples determine the strict labels
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, a nonzero level $N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ with $\Phi(j, j_q) = 0$), a witness `hKr` that the reduction of $\Phi$ modulo $q$ equals $(C X^q - X)(C X - X^q)$, and witnesses `hα`, `hβ` that the two degeneracy maps `heckeAlphaBar`, `heckeBetaBar` at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Assume the genus $\dim_k H^1(0)$ of the function field $k(j_q, j_{qN})$ over $k$, namely `modularFunctionFieldC k N`, is not positive, and that $q \nmid N$. Let $P$ and $P'$ be two place specializations for these same data, and let $R$ be a prolongation tuple for $P$ and $R'$ one for $P'$, each satisfying `IsModel`, i.e. the two divisor laws and the cusp laws at $\infty$ and at $0$. Then for every place $V$ of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$: the conjunction $\varphi(\mathrm{red}_1 V) = \mathrm{red}_2 V$ and $\varphi^2(\mathrm{red}_1 V) \neq \mathrm{red}_1 V$ holds for $P$ if and only if it holds for $P'$, and likewise the conjunction $\mathrm{red}_1 V = \varphi(\mathrm{red}_2 V)$ and $\varphi^2(\mathrm{red}_2 V) \neq \mathrm{red}_2 V$ holds for $P$ if and only if it holds for $P'$; here $\mathrm{red}_1, \mathrm{red}_2$ are the two reduction maps on places attached to the specialization and $\varphi$ is `frobOnPlacesGeomLevel k N data hKr`.
--
--   This is a uniqueness statement for the combinatorics of the special fibre at $q$ of the modular curve of level $Nq$: the labelling of a place of the level-$Nq$ field as lying strictly on the first or the second Frobenius leg does not depend on which place specialization, equipped with a model prolongation tuple, is used to reduce it. It is the input to the one-sided regularity law for model prolongation tuples at levels prime to $q$, and, unlike the corresponding rigidity statement with order laws, it asserts only the agreement of the two strictness predicates and not the equality of the specializations themselves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_isStrictFst_iff_and_isStrictSnd_iff_of_isModel_of_isModel.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.isStrictFst_iff_and_isStrictSnd_iff_of_isModel_of_isModel
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    (hng : ¬ (0 < genusFF k ↥(modularFunctionFieldC k N))) (hqN : ¬ q ∣ N)
    (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel)
    (R' : PlaceSpecialization.ProlongationTuple P') (hmodel' : R'.IsModel) :
    (∀ V, P.IsStrictFst V ↔ P'.IsStrictFst V) ∧ (∀ V, P.IsStrictSnd V ↔ P'.IsStrictSnd V) := by sorry
