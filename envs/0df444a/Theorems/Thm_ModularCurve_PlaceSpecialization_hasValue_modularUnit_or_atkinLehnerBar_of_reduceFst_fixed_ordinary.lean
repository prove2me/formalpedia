-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_atkinLehnerBar_of_reduceFst_fixed_ordinary
-- name    : ModularCurve.PlaceSpecialization.hasValue_modularUnit_or_atkinLehnerBar_of_reduceFst_fixed_ordinary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/02395c72-ff0d-5b00-a985-77a9bf440233
-- title:
--   Sheet dichotomy for the modular unit at ordinary places
-- statement:
--   Fix a non-zero natural number $N$ and a prime $q$ with $q \nmid N$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ (the chosen algebraic closure of $\mathbb{Q}$), an algebraically closed field $k$ of characteristic $q$, and a ring homomorphism $\mathrm{red} : A \to k$; assume the function field `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$ has principal divisors, i.e. every non-zero element has an associated degree-zero divisor recording its orders at all places. Let `data` be a `ModularPolynomialData q`, that is a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions $(j, j_q)$, satisfying the Kronecker congruence `hKr`: the reduction of $\Phi$ modulo $q$ equals $(\,\mathrm{C}\,X^{q} - X)(\mathrm{C}\,X - X^{q})$. Let `hα`, `hβ` assert the integrality of the two degeneracy maps `heckeAlphaBar` and `heckeBetaBar` from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$, and let $P$ be a `PlaceSpecialization` for these data, providing in particular a map `P.sp` from places of the level-$N$ curve over $\overline{\mathbb{Q}}$ to places of `modularFunctionFieldC k N` compatible with the $j$- and $j_N$-coordinates. Let $u$ be an element of `modularFunctionFieldBar (N * q)` whose underlying Laurent series is the coefficientwise image of the modular unit series $\Delta \cdot (\Delta\!\circ\! q)^{-1}$ of level $q$, and let $W$ be a place of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$. Write $w = P.\mathrm{reduceFst}\,W$, the place of `modularFunctionFieldC k N` obtained by restricting $W$ along `heckeAlphaBar` and applying `P.sp`. Assume $w$ is fixed by the square of the geometric-level Frobenius operation `frobOnPlacesGeomLevel k N data hKr`, that $w$ is affine in the sense that both $j$ and $j_N$ lie in its valuation subring, and that $w$ is not supersingular, i.e. $w \notin$ `ssPlaces q N k`. Then exactly one of the following holds: there is $a \in A$ with $\mathrm{red}\,a \neq 0$ such that $u$ lies in the valuation subring of $W$ with residue the image of $a$; or there is such an $a$ for the image of $u$ under the partial Atkin–Lehner automorphism `ProlongationTuple.atkinLehnerBar N q` of `modularFunctionFieldBar (N * q)`. The conclusion is stated as the conjunction of the disjunction of the two alternatives and the negation of their conjunction.
--
--   This is the level-$N$ sheet-separation dichotomy on $X_0(Nq)$ for $q \nmid N$: at a place of the level-$Nq$ curve whose first reduction is affine, ordinary and fixed by the square of Frobenius, the modular unit of level $q$ and its transform under the partial Atkin–Lehner involution $w_q$ take $q$-adic unit values on complementary sheets, exactly one of the two alternatives occurring. It generalises the level-one statement in which $w_q$ is the Fricke involution, and is used to obtain non-negativity of the order of the first residue of the modular unit when no unit value is taken.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_atkinLehnerBar_of_reduceFst_fixed_ordinary.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.hasValue_modularUnit_or_atkinLehnerBar_of_reduceFst_fixed_ordinary
    {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] (hqN : ¬ q ∣ N)
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] [DecidableEq k] [IsAlgClosed k]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
    {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst W))
      = P.reduceFst W)
    (haff : IsAffineGeomPlace k N (P.reduceFst W)) (hord : P.reduceFst W ∉ ssPlaces q N k) :
    ((∃ a : A, red a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)) ∨
      (∃ a : A, red a ≠ 0 ∧ W.HasValue (ProlongationTuple.atkinLehnerBar N q u) (a : AlgebraicClosure ℚ))) ∧
    ¬ ((∃ a : A, red a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)) ∧
      (∃ a : A, red a ≠ 0 ∧ W.HasValue (ProlongationTuple.atkinLehnerBar N q u) (a : AlgebraicClosure ℚ))) := by sorry
