-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide_of_ne_of_ord_jQFun_nonneg
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide_of_ne_of_ord_jQFun_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/34765bde-22d9-58b7-836a-1ec23a4c4493
-- title:
--   Side identity at ∞-side places where j(q^q) is regular
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a natural number $N \neq 0$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Let `data` be a `ModularPolynomialData q`, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_{q})$ of $q$-expansions, and let `hKr` be the Kronecker congruence for it: $\Phi$ reduced modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$. Let `hα`, `hβ` assert that the two degeneracy maps `heckeAlphaBar`, `heckeBetaBar` from level $N$ to level $Nq$ over $\overline{\mathbb Q}$ are integral ring homomorphisms, and let $P$ be a `PlaceSpecialization A q N data hKr k red hα hβ`, whose component `sp` sends places of the level-$N$ function field over $\overline{\mathbb Q}$ to places of the level-$N$ function field over $k$, compatibly with the stated conditions on $j$ and on divisor classes. Assume $q \nmid N$. Then for every place $c$ of the level-$Nq$ function field over $\overline{\mathbb Q}$ such that: $c$ is $\infty$-side for $P$, i.e. $c$ is cuspidal for $P$ and some $\tau \in A$ with $\mathrm{red}(\tau) = 1$ is the value of `tInfty N q` at $c$; the twofold application of `frobOnPlacesGeomLevel k N data hKr` to $P.\mathrm{reduceSnd}\,c = \mathrm{sp}(c|_{\mathrm{heckeBetaBar}})$ does not return $P.\mathrm{reduceSnd}\,c$; and the order $c.\mathrm{ord}$ of `jQFun N q` (the element of the level-$Nq$ function field coming from the $q$-rescaled expansion of $j$) is nonnegative, one has $$P.\mathrm{reduceSnd}\,c = \mathrm{frobOnPlacesGeomLevel}\,k\,N\,\mathrm{data}\,\mathrm{hKr}\,(P.\mathrm{reduceFst}\,c),$$ where $P.\mathrm{reduceFst}\,c = \mathrm{sp}(c|_{\mathrm{heckeAlphaBar}})$ and `frobOnPlacesGeomLevel` is the transport of a place along the geometric Frobenius of the level-$N$ function field over $k$.
--
--   This is the main case of the identity relating the two reductions of an $\infty$-side place by the geometric Frobenius, in the analysis of the fibre at $q$ of the modular curve of level $Nq$ through the Kronecker congruence: the two extra hypotheses restrict attention to places of the cuspidal region where $\mathrm{jQFun}$ has no pole and whose second reduction is not fixed by the square of Frobenius, so that the Frobenius alternative of the specialization is resolved in one way only. It is cited by [`ModularCurve.PlaceSpecialization.ProlongationTuple.reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide), which removes these two restrictions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide_of_ne_of_ord_jQFun_nonneg.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide_of_ne_of_ord_jQFun_nonneg
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N) :
    ∀ c, IsInftySide P c →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd c)) ≠ P.reduceSnd c →
      0 ≤ c.ord (jQFun N q) →
      P.reduceSnd c = frobOnPlacesGeomLevel k N data hKr (P.reduceFst c) := by sorry
