-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary
-- name    : ModularCurve.PlaceSpecialization.hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/28292370-2219-56d6-87a6-238beea36bb6
-- title:
--   Sheet separation at ordinary places: u or w_q u has unit value
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$, $k$ an algebraically closed field of characteristic $q$, and $\mathrm{red} : A \to k$ a ring homomorphism; assume that every nonzero element of the level-$1\cdot q$ field $F =$ `modularFunctionFieldBar (1 * q)` (the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $1\cdot q$ inside Laurent series) has a degree-zero divisor recording its order at every place. Let `data` be a monic bivariate integral modular polynomial $\Phi$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, let `hKr` assert its Kronecker congruence, namely that its reduction modulo $q$ equals $(C X^{q} - X)(C X - X^{q})$, and let `hα`, `hβ` assert that the two Hecke maps $\alpha$, $\beta$ from level $1$ to level $q$ are integral ring homomorphisms. Let $P$ be a place specialisation of level $1$ at $q$ relative to these data, $u \in F$ an element whose Laurent expansion is the coefficientwise image of the modular unit series $\Delta/\Delta_q$ of level $q$, and $W$ a place of $F$ over $\overline{\mathbb{Q}}$. Assume the place $P.\mathrm{reduceFst}\,W$ of `modularFunctionFieldC k 1` obtained by restricting $W$ along $\alpha$ and specialising is fixed by the square of the geometric-level Frobenius operator on places, is affine in the sense that both geometric generators $j$ and $j_N$ lie in its valuation subring, and does not lie in the set of supersingular places `ssPlaces q 1 k`. Then exactly one of the following holds: there is $a \in A$ with $\mathrm{red}\,a \neq 0$ such that $u$ lies in the valuation subring of $W$ with residue the image of $a$; or there is such an $a$ for the Fricke transform `frickeInvolutionBar (1 * q) u` of $u$. The conclusion is stated as the disjunction together with the negation of the conjunction.
--
--   This is the separation of the two sheets of $X_0(q)$ in characteristic $q$ above the ordinary points: the two components of the reduction meet only at supersingular points, so above an ordinary, Frobenius-square-fixed affine point the places of the level-$q$ function field fall into two disjoint families, distinguished by whether the modular unit $\Delta/\Delta_q$ or its Fricke transform has a value that is a unit. It is used for the corresponding Atkin–Lehner formulation and for the statement that the first sheet is separated from its Fricke translate and that the two together cover all such places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary.lean

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
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type} [Field k]
    [CharP k q] [DecidableEq k] [IsAlgClosed k] [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))]
    {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (u : modularFunctionFieldBar (1 * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst W)) = P.reduceFst W)
    (haff : IsAffineGeomPlace k 1 (P.reduceFst W)) (hord : P.reduceFst W ∉ ssPlaces q 1 k) :
    ((∃ a : A, red a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)) ∨
      (∃ a : A, red a ≠ 0 ∧ W.HasValue (frickeInvolutionBar (1 * q) u) (a : AlgebraicClosure ℚ))) ∧
    ¬ ((∃ a : A, red a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)) ∧
      (∃ a : A, red a ≠ 0 ∧ W.HasValue (frickeInvolutionBar (1 * q) u) (a : AlgebraicClosure ℚ))) := by sorry
