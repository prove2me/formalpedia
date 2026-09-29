-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary_univ
-- name    : ModularCurve.PlaceSpecialization.hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/58b0ecdf-43fc-5a97-a4a2-fb1ec5c74497
-- title:
--   Sheet separation at ordinary places via the modular unit
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$, $k$ an algebraically closed field of characteristic $q$, and $\mathrm{red}\colon A \to k$ a ring homomorphism; assume that every nonzero element of the field $F = \overline{\mathbb{Q}}\otimes$-base change of the full level-$1\cdot q$ modular function field inside $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ admits a divisor of degree $0$ recording its order at every place. Let `data` consist of a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, satisfying the Kronecker congruence $\Phi \bmod q = (X^q - Y)(X - Y^q)$, let $h\alpha$, $h\beta$ assert integrality of the Hecke $\alpha$- and $\beta$-maps from level $1$ to level $q$ over $\overline{\mathbb{Q}}$, and let $P$ be a place-specialization datum for $A$, $q$, level $1$, these data, $k$ and $\mathrm{red}$. Let $u \in F$ have Laurent expansion the coefficientwise image of $\Delta/\Delta_{(q)} =$ `modularUnitSeries q`, and let $W$ be a place of $F$ over $\overline{\mathbb{Q}}$ whose specialized place $P.\mathrm{reduceFst}\,W$ of the level-$1$ function field over $k$ is fixed by the square of the geometric-level Frobenius operation on places, is affine (both generators $j$, $j_N$ lie in its valuation subring), and is not a supersingular place. Then exactly one of the following holds: there is $a \in A$ with $\mathrm{red}\,a \neq 0$ such that $u$ lies in the valuation subring of $W$ with residue the image of $a$; or the same holds for the Fricke transform $\mathrm{frickeInvolutionBar}(1\cdot q)\,u$ of $u$. (The conclusion is stated as the disjunction together with the negation of the conjunction.)
--
--   This is the separation of the two sheets of $X_0(q)$ in characteristic $q$ above the ordinary points: at a place whose reduction is an ordinary affine point fixed by the square of Frobenius, the modular unit $\Delta/\Delta_{(q)}$ takes a unit value on precisely one of the two components, the other component being detected by its Fricke transform. It feeds the computation of the order of the residue of the modular unit along the first sheet in [`ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary_univ.lean

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

theorem ModularCurve.PlaceSpecialization.hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary_univ
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
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
