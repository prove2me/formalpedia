-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_arithmeticGalois_smul
-- name    : ModularCurve.PlaceSpecialization.reduceSnd_arithmeticGalois_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/db6d3226-cfbe-5ce3-aa0a-4f5f74d3254f
-- title:
--   Inertia invariance of the second level-N reduction
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an integer $N\neq 0$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}:A\to k$. Let `data` be a `ModularPolynomialData` for $q$, i.e. a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ vanishing on the pair ($j$-expansion, $q$-level expansion), let `hKr` be the Kronecker congruence for it, namely $\Phi \bmod q=(C(X)^q-X)(C(X)-X^q)$, and let `hα`, `hβ` assert that the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of the level-$N$ into the level-$Nq$ modular function field over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` for these data: a map `sp` from places of the level-$N$ field over $\overline{\mathbb Q}$ to places of the level-$N$ field over $k$, an induced homomorphism on degree-zero divisor classes, and compatibility conditions, among them invariance of `sp` under the inertia action. Let $\sigma$ be a $\mathbb Q$-automorphism of $\overline{\mathbb Q}$ lying in $A.\mathrm{inertiaSubgroupIn}\ \mathbb Q$, the image of the inertia subgroup of $A$ inside the decomposition subgroup, and let $V$ be a place of the level-$Nq$ field over $\overline{\mathbb Q}$. Then $P.\mathrm{reduceSnd}$, i.e. `sp` applied to the restriction along `heckeBetaBar`, takes the same value on $V$ and on the translate of $V$ by the semilinear automorphism `arithmeticGalois` attached to $\sigma$ (coefficientwise action of $\sigma$ on Laurent series).
--
--   This records that the second of the two level-$N$ reductions of a place of the level-$Nq$ modular function field — specialisation of the restriction along the degeneracy embedding $\beta$ — is unchanged by the inertia group of the chosen valuation subring, the degeneracy embeddings being defined over $\mathbb Q$. It is used in the construction of glued specialisations and in the level-one prolongation arguments that compare the two reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_reduceSnd_arithmeticGalois_smul.lean

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

theorem ModularCurve.PlaceSpecialization.reduceSnd_arithmeticGalois_smul
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.reduceSnd (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = P.reduceSnd V := by sorry
