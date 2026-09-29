-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.not_isInftySide_of_isZeroSide
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/c9807329-484c-5a02-bfc4-5bf9a8bb5740
-- title:
--   Zero side and infinity side of a place are disjoint
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive level $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix moreover modular polynomial data `data` for $q$ (a monic bivariate integral polynomial $\Phi$ of degree $\psi(q)$ vanishing on the pair of $q$-expansions of $j$), a proof `hKr` that $\Phi$ reduces modulo $q$ to $(X'^q - X)(X' - X^q)$ in Kronecker's form, and proofs `hα`, `hβ` that the two Hecke maps $\alpha$, $\beta$ at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Let $P$ be a place specialization of these data, i.e. a compatible system transporting places and degree-zero divisor classes of the level-$N$ modular function field over $\overline{\mathbb{Q}}$ to the level-$N$ function field over $k$, and let $W$ be a place of the level-$Nq$ function field $\mathrm{modularFunctionFieldBar}(N q)$ over $\overline{\mathbb{Q}}$ (a proper valuation subring containing $\overline{\mathbb{Q}}$ and a principal ideal ring). Assume $W$ lies on the zero side for $P$: the predicate `IsCuspidal'` holds for $P$ and $W$, and there is $\tau \in A$ with $\mathrm{red}\,\tau = 1$ such that $t_0 = \mathrm{tZero}\,N\,q$ lies in the valuation ring of $W$ with residue the image of $\tau$. Then $W$ does not lie on the infinity side: it is not the case that `IsCuspidal` holds for $P$ and $W$ and that some $\tau \in A$ with $\mathrm{red}\,\tau = 1$ has $t_\infty = \mathrm{tInfty}\,N\,q$ taking the value $\tau$ at $W$.
--
--   The two chart conditions $\mathrm{IsZeroSide}$ and $\mathrm{IsInftySide}$ single out the places of the level-$Nq$ modular function field lying over the two components of the special fibre of $X_0(Nq)$ at $q$, as in the Deligne–Rapoport description; this statement records that the two sides are mutually exclusive. It is used in the analysis of cuspidal places and of regularity and ordinarity laws for prolongation tuples, where a case distinction between the two components must be known to be exhaustive and disjoint.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.not_isInftySide_of_isZeroSide
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hW : ProlongationTuple.IsZeroSide P W) :
    ¬ ProlongationTuple.IsInftySide P W := by sorry
