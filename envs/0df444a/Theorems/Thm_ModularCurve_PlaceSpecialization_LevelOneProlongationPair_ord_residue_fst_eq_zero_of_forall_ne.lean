-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residue_fst_eq_zero_of_forall_ne
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ord_residue_fst_eq_zero_of_forall_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/a2c53bbb-ae54-5a1e-a782-d40f335c7d1d
-- title:
--   Order of the first residue at non-geometric places
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ (with decidable equality on $\mathrm{RatFunc}\,k$) and a ring homomorphism $red : A \to k$; fix further modular data at level $q$, namely $data$ consisting of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ vanishing on the pair of $q$-expansions of $j$, a proof $hKr$ that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, and proofs $h\alpha$, $h\beta$ that the two Hecke maps $\overline\alpha$, $\overline\beta$ at level $1$ and prime $q$ are integral ring homomorphisms over $\overline{\mathbb Q}$. Let $P$ be a place specialisation for these data and $R$ a level-one prolongation pair attached to $P$ (a residue homomorphism $\overline{red} : \mathrm{ResidueField}\,A \to k$ lifting $red$, the coefficientwise embedding $\iota$ of the level-one full modular function field over $\mathrm{ResidueField}\,A$ into $\mathrm{modularFunctionFieldC}\,k\,1$, and two regular prolongations $R_1$, $R_2$ of the level-$q$ field exchanged by the Fricke involution, with the stated residue compatibilities). Let $g$ be an element of `R.R₁.integers`, and let $v$ be a place of $\mathrm{modularFunctionFieldC}\,k\,1$ over $k$ such that $v \neq$ `charLGeomPlaceOfPoint k a` for every $a \in k$ and $v$ is not the transport of the infinite place of $\mathrm{RatFunc}\,k$ along `charLGeomPlaceEquiv`. Then $\mathrm{ord}_v(\mathrm{residue}_1\,g) = 0$, where $\mathrm{ord}_v$ is minus the logarithm of the $v$-adic valuation.
--
--   The level-one special fibre is a rational curve: its places over $k$ are exhausted by the points $\tilde\jmath = a$ with $a \in k$ together with the pole of $\tilde\jmath$, so the two hypotheses on $v$ are in fact contradictory and the asserted vanishing of the order holds vacuously. In this shape the statement serves as a uniform boundary case in the divisor bookkeeping for the two branches of the reduced modular curve, and is cited by the per-branch divisor law and by the criteria for membership in the second prolongation and for non-negativity of orders away from the cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residue_fst_eq_zero_of_forall_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ord_residue_fst_eq_zero_of_forall_ne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq (RatFunc k)] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (g : R.R₁.integers) (v : Place k (modularFunctionFieldC k 1))
    (hv : ∀ a : k, v ≠ charLGeomPlaceOfPoint k a)
    (hv' : v ≠ charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k)) :
    v.ord (R.residue₁ g) = 0 := by sorry
