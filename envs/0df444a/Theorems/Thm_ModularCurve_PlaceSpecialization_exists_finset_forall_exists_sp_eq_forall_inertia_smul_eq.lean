-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq
-- name    : ModularCurve.PlaceSpecialization.exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/afca7ffc-9273-5154-97ba-f8c9640be848
-- title:
--   Inertia-invariant lifting of all but finitely many places
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $N$ be a nonzero natural number, let $k$ be an algebraically closed field of characteristic $q$, let $\mathrm{red} : A \to k$ be a ring homomorphism, let `data` consist of a monic $\Phi \in (\mathbb{Z}[X])[Y]$ of degree $\psi(q)$ with $\Phi(j, j_q) = 0$, let `hKr` assert the Kronecker congruence $\overline{\Phi} = (X^q - Y)(X - Y^q)$ modulo $q$, and let `hα`, `hβ` assert that the two Hecke inclusions of the base-changed modular function field of level $N$ into that of level $Nq$ are integral. Let $P$ be a term of `PlaceSpecialization` for these data, which in particular provides a map `P.sp` from places of $\overline{\mathbb{Q}}(X_0(N))$, realised as `modularFunctionFieldBar N`, to places of `modularFunctionFieldC k N` $= k(\tilde{\jmath}, \tilde{\jmath}_N)$, an additive map on degree-zero divisor class groups, and clauses comparing orders of $j$, $j_N$ and their translates with those of their reductions. Assume $q \nmid N$. Then there is a finite set $X$ of places of `modularFunctionFieldC k N` over $k$ such that every place $v \notin X$ is of the form $v = P.\mathrm{sp}(u)$ for some place $u$ of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ which is fixed by the action of `arithmeticGalois (modularFunctionFieldFull N) σ` — the coefficientwise semilinear automorphism attached to $σ$ — for every $σ$ in the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $A$ over $\mathbb{Q}$.
--
--   This is the cofinite form of unramified lifting of points for $X_0(N)$ at a prime $q \nmid N$ of good reduction: away from a finite exceptional set, $k$-points of the special fibre are specializations of points defined over the inertia-fixed field. It is used in the construction of glued specializations and of the prolongation data for level structures, where divisor classes may be moved away from the excluded places at no cost.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq.lean

import Definitions.Def_ModularCurve_GlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N) :
    ∃ X : Finset (Place k (modularFunctionFieldC k N)),
      ∀ v : Place k (modularFunctionFieldC k N), v ∉ X →
        ∃ u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          P.sp u = v ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull N) σ • u = u := by sorry
