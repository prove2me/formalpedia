-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq
-- name    : ModularCurve.PlaceSpecialization.exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/322aec73-3055-50ba-a8cf-06c3ceb0903a
-- title:
--   Inertia-fixed lift of the second kind over a given place
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, a field $k$ of characteristic $q$, and a ring homomorphism $\mathrm{red} : A \to k$. Let $data$ be a `ModularPolynomialData` for $q$, i.e. a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions, let $hKr$ assert the Kronecker congruence that $\Phi$ reduced modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, and let $h\alpha$, $h\beta$ assert that the two degeneracy algebra maps $\overline{\alpha}, \overline{\beta}$ from level $N$ to level $Nq$ (over $\overline{\mathbb Q}$, on the Laurent-series models of the modular function fields) are integral. Let $P$ be a `PlaceSpecialization` for these data, with specialisation map $\mathrm{sp}$ from places of the level-$N$ modular function field over $\overline{\mathbb Q}$ to places of the level-$N$ modular function field over $k$, and write $\varphi$ for `frobOnPlacesGeomLevel`, the Frobenius operation on the latter places determined by $data$ and $hKr$. Let $u$ be a place of the level-$N$ field over $\overline{\mathbb Q}$ such that $\varphi(\varphi(\mathrm{sp}\,u)) \ne \mathrm{sp}\,u$, and such that $u$ is fixed by the semilinear action `arithmeticGalois` of every $\sigma$ in the image of the inertia subgroup of $A$ over $\mathbb Q$ inside $\overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$. Then there is a place $V$ of the level-$Nq$ field over $\overline{\mathbb Q}$ satisfying: $P.\mathrm{IsStrictSnd}\,V$, that is $P.\mathrm{reduceFst}\,V = \varphi(P.\mathrm{reduceSnd}\,V)$ and $\varphi(\varphi(P.\mathrm{reduceSnd}\,V)) \ne P.\mathrm{reduceSnd}\,V$; the restriction of $V$ along $\overline{\beta}$ equals $u$; $P.\mathrm{reduceSnd}\,V$, i.e. $\mathrm{sp}$ of that restriction, equals $\mathrm{sp}\,u$; and $V$ is fixed by `arithmeticGalois` at level $Nq$ for every $\sigma$ in the same inertia image.
--
--   In the Deligne–Rapoport picture of the special fibre of $X_0(Nq)$ at a prime $q \nmid N$ — two copies of $X_0(N)$ crossing at the supersingular points — this produces an inertia-invariant point of $X_0(Nq)$ over a prescribed inertia-invariant point $u$ of $X_0(N)$ whose reduction is of Frobenius type on the second component and lies away from the $\varphi^2$-fixed locus. It feeds the construction of glued specialisations and prolongation tuples used later in the level-changing argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq.lean

import Definitions.Def_ModularCurve_GlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hu : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp u)) ≠ P.sp u)
    (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull N) σ • u = u) :
    ∃ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictSnd V ∧
        V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ = u ∧
        P.reduceSnd V = P.sp u ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V := by sorry
