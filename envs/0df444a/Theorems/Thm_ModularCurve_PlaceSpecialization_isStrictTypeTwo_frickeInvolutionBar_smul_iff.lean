-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictTypeTwo_frickeInvolutionBar_smul_iff
-- name    : ModularCurve.PlaceSpecialization.isStrictTypeTwo_frickeInvolutionBar_smul_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/46a2eb5d-bb7f-5fa1-b87b-a2a17c09ecf5
-- title:
--   Fricke involution exchanges strict types one and two
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Let `data` be a `ModularPolynomialData q`, i.e. a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, and let `hKr` assert the Kronecker congruence that the reduction of $\Phi$ modulo $q$ equals $(C X^{q} - X)(C X - X^{q})$; let `hα`, `hβ` assert that the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` from level $1$ into level $1\cdot q$ over $\overline{\mathbb Q}$ are integral ring maps. Let $P$ be a term of `PlaceSpecialization A q 1 data hKr k red hα hβ`, and let $W$ be a place of the geometric modular function field `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$. Writing $\Phi_{\mathrm{geom}}$ for `frobOnPlacesGeomLevel k 1 data hKr` and $\mathrm{red}_1, \mathrm{red}_2$ for `P.redFst`, `P.redSnd`, the conclusion is an equivalence: the translate of $W$ by the Fricke automorphism `frickeInvolutionBar (1 * q)` satisfies $\mathrm{red}_1 = \Phi_{\mathrm{geom}}(\mathrm{red}_2)$ together with $\Phi_{\mathrm{geom}}^{2}(\mathrm{red}_2) \ne \mathrm{red}_2$, if and only if $W$ itself satisfies $\Phi_{\mathrm{geom}}(\mathrm{red}_1) = \mathrm{red}_2$ together with $\Phi_{\mathrm{geom}}^{2}(\mathrm{red}_1) \ne \mathrm{red}_1$.
--
--   This records, at the level of places and their specialisations, the classical fact that the Fricke (Atkin–Lehner) involution $w_q$ interchanges the two components of the special fibre of $X_0(q)$ in characteristic $q$: it swaps the two strictness conditions attached to the two reductions of a place. It is used in the analysis of the charts of the multiplicative covering, in particular to separate the cusp at infinity from the domain of the zero chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_isStrictTypeTwo_frickeInvolutionBar_smul_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.isStrictTypeTwo_frickeInvolutionBar_smul_iff
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.IsStrictTypeTwo (frickeInvolutionBar (1 * q) • W) ↔ P.IsStrictTypeOne W := by sorry
