-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_pic0Mk_eq_zero_of_isGoodDiv_of_mk_glueData_eq_zero_of_nsmul_eq_zero_of_isModel_levelOne
-- name    : ModularCurve.PlaceSpecialization.pic0Mk_eq_zero_of_isGoodDiv_of_mk_glueData_eq_zero_of_nsmul_eq_zero_of_isModel_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/ceb24cb5-9b65-5902-bac3-85491a59c233
-- title:
--   Prime-to-q torsion with trivial glued reduction vanishes, level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions) satisfying the Kronecker congruence $\Phi \equiv (C(X)^q - X)(C(X) - X^q)$ modulo $q$, and integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy maps from level $1$ to level $1\cdot q$ over $\overline{\mathbb{Q}}$. Let $P$ be a place-specialisation datum at auxiliary level $N = 1$ for these choices, let $W$ be a finite set of places of the level-$1$ function field over $k$ consisting exactly of the supersingular places (rational affine geometric places whose $j$-value lies in the supersingular set), and let $R$ be a prolongation tuple for $P$ satisfying `IsModel` (the divisor laws on both sides together with the two cusp laws), the regularity law and node-value law relative to $W$, and the fixed-place order law. Let $D$ be a degree-zero divisor on the level-$1\cdot q$ function field over $\overline{\mathbb{Q}}$ such that every place in the support of $D$ is strict for the first or for the second reduction map, and such that the associated glue datum $(\mathrm{mapDomain}\,P.\mathrm{reduceFst}(D|_{\text{strict fst}}),\ \mathrm{mapDomain}\,P.\mathrm{reduceSnd}(D|_{\text{strict snd}}),\ 0)$ for the node pairs obtained from $W$ by the arithmetic Frobenius semilinear automorphism is admissible and has trivial class in the glued degree-zero Picard group. If moreover $n$ is a nonzero natural number not divisible by $q$ with $n \cdot [D] = 0$ in $\mathrm{Pic}^0$, then $[D] = 0$.
--
--   This is the injectivity statement underlying the specialisation of prime-to-$q$ torsion of the Jacobian of $X_0(q)$ into the Picard group of the glued (two copies of $X_0(1)$ crossing at the supersingular points) special fibre: a prime-to-$q$ torsion class whose glued reduction vanishes is itself zero. It is used in the proof that, for prime-to-$q$ torsion, the difference $\sigma x - x$ lands in the inertia invariants at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_pic0Mk_eq_zero_of_isGoodDiv_of_mk_glueData_eq_zero_of_nsmul_eq_zero_of_isModel_levelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.pic0Mk_eq_zero_of_isGoodDiv_of_mk_glueData_eq_zero_of_nsmul_eq_zero_of_isModel_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hgood : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))))
    (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W)
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W))
    (hmk : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W)
        ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W)
          (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadm⟩ = 0)
    (n : ℕ) (hn : n ≠ 0) (hqn : ¬ q ∣ n) (hnD : n • Pic0.mk D = 0) :
    Pic0.mk D = 0 := by sorry
