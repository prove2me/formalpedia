-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceSnd_filter_sheetTwo_eq_ord_residueSnd_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceSnd_filter_sheetTwo_eq_ord_residueSnd_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/a9eb6aef-16fc-5f07-87f4-b12d26a5b3b3
-- title:
--   Second-sheet divisor law at ordinary φ²-fixed places, level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence $\Phi \bmod q = (X^q - Y)(X - Y^q)$, and the hypotheses `hα`, `hβ` that the two degeneracy embeddings $\overline{\mathcal{F}}_1 \to \overline{\mathcal{F}}_{1\cdot q}$ of modular function fields over $\overline{\mathbb{Q}}$ are integral; the field $\overline{\mathcal{F}}_{1\cdot q}$ is assumed to have principal divisors. Let $P$ be a place specialisation at level $1$ for these data, $R$ a prolongation tuple for $P$ satisfying `IsModel` (the two divisor laws at places not fixed by the square of the geometric-level Frobenius operation on places, together with the two cusp laws) and `OrderLawFixed`, and let $u \in \overline{\mathcal{F}}_{1\cdot q}$ be an element whose Laurent series is the coefficientwise image of $\Delta(q\text{-series})\cdot(\Delta$ after $q$-substitution$)^{-1}$. The assertion is: for every $f \in \overline{\mathcal{F}}_{1\cdot q}$ lying in the integers of the second prolongation $R_2$ and with nonzero $R_2$-residue, for every divisor $D$ with $D(W) = \operatorname{ord}_W f$ at all places $W$, and for every place $v$ of the level-one function field over $k$ which is fixed by the square of the Frobenius operation on places, which is affine (both $j$ and $j_N$ lie in its valuation subring) and which is not supersingular, the pushforward along $P.\mathrm{reduceSnd}$ (specialisation of the restriction along the second degeneracy map) of the restriction of $D$ to those $W$ such that $P.\mathrm{reduceSnd}\,W$ is fixed by the square of the Frobenius operation, affine and not supersingular, and such that $(w_q u)$ has at $W$ a value congruent to some $a \in A$ with $\mathrm{red}\,a \neq 0$, takes at $v$ the value $\operatorname{ord}_v$ of the second residue of $f$.
--
--   This is the divisor law on the second component of the special fibre of $X_0(q)$ at ordinary places fixed by the square of Frobenius, the Atkin–Lehner mirror of the corresponding first-sheet statement, the two sheets being separated by the valuation of the Fricke transform of the modular unit $\Delta/\Delta_q$. It is used in the computation of the component-group contribution in `componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_levelOne_of_five_le`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceSnd_filter_sheetTwo_eq_ord_residueSnd_levelOne.lean

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

open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceSnd_filter_sheetTwo_eq_ord_residueSnd_levelOne
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] [DecidableEq k] [IsAlgClosed k] [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))]
    {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (u : modularFunctionFieldBar (1 * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q)) :
    ∀ (f : modularFunctionFieldBar (1 * q)) (h₂ : f ∈ R.R₂.integers),
      R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
        (∀ W, D W = W.ord f) →
        ∀ v : Place k (modularFunctionFieldC k 1),
          frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
          IsAffineGeomPlace k 1 v → v ∉ ssPlaces q 1 k →
          Finsupp.mapDomain P.reduceSnd
              (D.filter fun W => ((frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceSnd W)) = P.reduceSnd W ∧
        IsAffineGeomPlace k 1 (P.reduceSnd W) ∧ P.reduceSnd W ∉ ssPlaces q 1 k) ∧
        (∃ a : A, red a ≠ 0 ∧ W.HasValue (frickeInvolutionBar (1 * q) u) (a : AlgebraicClosure ℚ)))) v
            = v.ord (R.residue₂ ⟨f, h₂⟩) := by sorry
