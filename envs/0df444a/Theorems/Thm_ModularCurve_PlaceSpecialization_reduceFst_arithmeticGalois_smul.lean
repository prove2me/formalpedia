-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_arithmeticGalois_smul
-- name    : ModularCurve.PlaceSpecialization.reduceFst_arithmeticGalois_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/9eca191f-f930-5a32-8a1a-ef46de5fa8c3
-- title:
--   Inertia invariance of the first level-N reduction
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, a positive integer $N$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Fix furthermore a `ModularPolynomialData` for $q$, i.e. a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the level-$q$ expansion, together with a proof `hKr` of the Kronecker congruence $\Phi \bmod q = (X^{q}-Y)(X-Y^{q})$ for it, and proofs `hα`, `hβ` that the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of the level-$N$ field into the level-$Nq$ field over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` for these data: a map `sp` sending places of `modularFunctionFieldBar N` (the base change to $\overline{\mathbb Q}$ of `modularFunctionFieldFull N`) to places of `modularFunctionFieldC k N`, a homomorphism on degree-zero divisor class groups, and the list of compatibility axioms (among them an inertia-invariance clause) contained in that structure. Let $\sigma$ be a $\mathbb Q$-automorphism of $\overline{\mathbb Q}$ lying in `A.inertiaSubgroupIn ℚ`, the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ inside its decomposition subgroup, and let $V$ be a place of `modularFunctionFieldBar (N * q)`, i.e. a valuation subring containing $\overline{\mathbb Q}$, not the whole field, and a principal ideal ring. Then $P$'s first reduction, $W \mapsto$ `sp` of the restriction of $W$ along `heckeAlphaBar`, takes the same value at $V$ and at the translate of $V$ by the semilinear automorphism `arithmeticGalois (modularFunctionFieldFull (N * q)) σ` attached to $\sigma$.
--
--   The two degeneracy maps $X_0(Nq) \to X_0(N)$ are defined over $\mathbb Q$, so the two level-$N$ reductions of a place of the level-$Nq$ function field are compatible with the arithmetic Galois action; combined with the inertia-invariance clause of a place specialisation, this says that the first reduction is constant on inertia orbits. The statement is used repeatedly in the analysis of glued specialisations and of level-one prolongation pairs, where representatives of divisor classes must be chosen inertia-equivariantly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_reduceFst_arithmeticGalois_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_GlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.reduceFst_arithmeticGalois_smul
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.reduceFst (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = P.reduceFst V := by sorry
